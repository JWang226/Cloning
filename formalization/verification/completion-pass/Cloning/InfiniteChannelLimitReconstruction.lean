import Cloning.InfiniteChannelWeakLimit
import Cloning.InfiniteChannelTraceRepair

/-! Reconstruction of an actual trace-class linear map from bounded-operator coefficient
limits. Linearity and the trace-class range are derived. Positivity and the uniform positive
trace bound, rather than trace preservation, suffice. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma operator_limit_add
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (T : TraceClass H → K →L[ℂ] K)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (L n A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ))
    (A B : TraceClass H) : T (A + B) = T A + T B := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hinc (U V : TraceClass K) : (U + V).1 = U.1 + V.1 := inclusionCLM.map_add U V
  have hadd : Tendsto (fun n => ⟪x, (L n (A + B)).1 y⟫_ℂ) atTop
      (𝓝 ⟪x, (T A + T B) y⟫_ℂ) := by
    have h := (hlim A x y).add (hlim B x y)
    simpa only [map_add, hinc, ContinuousLinearMap.add_apply, inner_add_right] using h
  exact tendsto_nhds_unique (hlim (A + B) x y) hadd

lemma operator_limit_smul
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (T : TraceClass H → K →L[ℂ] K)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (L n A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ))
    (c : ℂ) (A : TraceClass H) : T (c • A) = c • T A := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hinc (z : ℂ) (U : TraceClass K) : (z • U).1 = z • U.1 := inclusionCLM.map_smul z U
  have hsmul : Tendsto (fun n => ⟪x, (L n (c • A)).1 y⟫_ℂ) atTop
      (𝓝 ⟪x, (c • T A) y⟫_ℂ) := by
    have h := (hlim A x y).const_mul c
    simpa only [map_smul, hinc, ContinuousLinearMap.smul_apply, inner_smul_right] using h
  exact tendsto_nhds_unique (hlim (c • A) x y) hsmul

def operatorLimitLinearMap
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (T : TraceClass H → K →L[ℂ] K)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (L n A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ)) :
    TraceClass H →ₗ[ℂ] (K →L[ℂ] K) where
  toFun := T
  map_add' := operator_limit_add L T hlim
  map_smul' := operator_limit_smul L T hlim

lemma positive_operator_limit_properties
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (T : TraceClass H → K →L[ℂ] K) (c : ℝ)
    (hpos : ∀ n A, 0 ≤ A.1 → 0 ≤ (L n A).1)
    (htrace : ∀ n A, 0 ≤ A.1 → (traceCLM (L n A)).re ≤ c * (traceCLM A).re)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (L n A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ))
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    0 ≤ T A ∧ ∃ hTA : IsTraceClass (T A), (trace (T A) hTA).re ≤ c * (traceCLM A).re := by
  have hdiag (x : K) : Tendsto (fun n => ⟪(L n A).1 x, x⟫_ℂ) atTop
      (𝓝 ⟪T A x, x⟫_ℂ) := by
    convert (hlim A x x).star using 1
    · ext n; exact (inner_conj_symm _ _).symm
    · congr 1; exact (inner_conj_symm _ _).symm
  exact InfiniteTraceClassWeakLimit.traceClass_of_diagonal_tendsto
    (fun n => (L n A).1) (T A) (fun n => hpos n A hA) (fun n => (L n A).2)
    (c * (traceCLM A).re) (fun n => htrace n A hA) hdiag

lemma isTraceClass_operator_limit
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (T : TraceClass H → K →L[ℂ] K) (c : ℝ)
    (hpos : ∀ n A, 0 ≤ A.1 → 0 ≤ (L n A).1)
    (htrace : ∀ n A, 0 ≤ A.1 → (traceCLM (L n A)).re ≤ c * (traceCLM A).re)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (L n A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ))
    (A : TraceClass H) : IsTraceClass (T A) := by
  let F := operatorLimitLinearMap L T hlim
  have hpositive (B : TraceClass H) (hB : 0 ≤ B.1) : IsTraceClass (F B) :=
    (positive_operator_limit_properties L T c hpos htrace hlim B hB).2.choose
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) : IsTraceClass (F B) := by
    rw [← TraceClass.positivePart_sub_negativePart B hB, map_sub]
    simpa only [sub_eq_add_neg] using isTraceClass_add
      (hpositive _ (TraceClass.positivePart_nonneg B hB))
      (isTraceClass_neg (hpositive _ (TraceClass.negativePart_nonneg B hB)))
  change IsTraceClass (F A)
  rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A, map_add, map_smul]
  exact isTraceClass_add
    (hself _ (TraceClass.realComponent_isSelfAdjoint A))
    (isTraceClass_smul Complex.I (hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)))

/-- The raw operator family really is a complex-linear map into trace class. -/
theorem exists_linearMap_of_coefficient_limit
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K)
    (T : TraceClass H → K →L[ℂ] K) (c : ℝ)
    (hpos : ∀ n A, 0 ≤ A.1 → 0 ≤ (L n A).1)
    (htrace : ∀ n A, 0 ≤ A.1 → (traceCLM (L n A)).re ≤ c * (traceCLM A).re)
    (hlim : ∀ A x y, Tendsto (fun n => ⟪x, (L n A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ)) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K, ∀ A, (Ψ A).1 = T A := by
  let F := operatorLimitLinearMap L T hlim
  refine ⟨{
    toFun := fun A => TraceClass.ofOperator (T A) (isTraceClass_operator_limit L T c hpos htrace hlim A)
    map_add' := ?_
    map_smul' := ?_ }, fun A => rfl⟩
  · intro A B
    exact Subtype.ext (F.map_add A B)
  · intro z A
    exact Subtype.ext (F.map_smul z A)

end
end Cloning.InfiniteTraceClass
