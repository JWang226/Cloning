import Cloning.InfiniteChannelTraceRepair
import Cloning.InfiniteTraceClassDecomposition

/-! Actual trace-class conjugation between different Hilbert spaces.
Trace-class membership is proved from rank-one series, rather than assuming a
rectangular operator-ideal API. Isometric conjugation is an actual CPTP map. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ComplexOrder InnerProductSpace Topology BigOperators

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Rectangular conjugation as a continuous map on bounded operators. -/
def operatorConjugation (V : H →L[ℂ] K) : (H →L[ℂ] H) →L[ℂ] (K →L[ℂ] K) :=
  ((ContinuousLinearMap.compL ℂ K H K).flip V.adjoint).comp
    (ContinuousLinearMap.compL ℂ H H K V)

@[simp] lemma operatorConjugation_apply (V : H →L[ℂ] K) (A : H →L[ℂ] H) (x : K) :
    operatorConjugation V A x = V (A (V.adjoint x)) := rfl

lemma operatorConjugation_rankOne (V : H →L[ℂ] K) (x : H) :
    operatorConjugation V (InnerProductSpace.rankOne ℂ x x) =
      InnerProductSpace.rankOne ℂ (V x) (V x) := by
  ext y
  change V (⟪x, V.adjoint y⟫_ℂ • x) = ⟪V x, y⟫_ℂ • V x
  rw [map_smul, ContinuousLinearMap.adjoint_inner_right]

lemma operatorConjugation_nonneg (V : H →L[ℂ] K) (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    0 ≤ operatorConjugation V A := by
  apply nonneg_of_inner_nonneg
  intro x
  change 0 ≤ ⟪x, V (A (V.adjoint x))⟫_ℂ
  rw [← V.adjoint_inner_left]
  exact (A.nonneg_iff_isPositive.mp hA).inner_nonneg_right (V.adjoint x)

lemma summable_conjugated_positive_vectors (V : H →L[ℂ] K)
    (A : TraceClass H) (hA : 0 ≤ A.1) {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => vectorProjector (V (CFC.sqrt A.1 (b i)))) := by
  have hm := (positive_rankOne_mass hA A.2 b).summable
  apply (hm.mul_left (‖V‖ ^ 2)).of_norm_bounded
  intro i
  simp only [norm_vectorProjector]
  calc
    ‖V (CFC.sqrt A.1 (b i))‖ ^ 2 ≤ (‖V‖ * ‖CFC.sqrt A.1 (b i)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (V.le_opNorm _)
    _ = _ := mul_pow _ _ 2

lemma conjugated_positive_vectors_tsum_coe (V : H →L[ℂ] K)
    (A : TraceClass H) (hA : 0 ≤ A.1) {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, vectorProjector (V (CFC.sqrt A.1 (b i)))).1 =
      operatorConjugation V A.1 := by
  have hleft := (summable_conjugated_positive_vectors V A hA b).hasSum.mapL inclusionCLM
  have hright := ((positive_rankOne_series hA A.2 b).mapL inclusionCLM).mapL
    (operatorConjugation V)
  have hright' : HasSum (fun i : w => inclusionCLM
      (vectorProjector (V (CFC.sqrt A.1 (b i))))) (operatorConjugation V A.1) := by
    simpa only [inclusionCLM_apply, vectorProjector, TraceClass.ofOperator_coe,
      operatorConjugation_rankOne] using hright
  exact hleft.unique hright'

lemma isTraceClass_operatorConjugation_of_nonneg (V : H →L[ℂ] K)
    (A : TraceClass H) (hA : 0 ≤ A.1) : IsTraceClass (operatorConjugation V A.1) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [← conjugated_positive_vectors_tsum_coe V A hA b]
  exact (∑' i : w, vectorProjector (V (CFC.sqrt A.1 (b i)))).2

/-- A bounded rectangular conjugation preserves trace class. This ideal
property is proved for the actual bounded operator `V A V†`. -/
theorem isTraceClass_operatorConjugation (V : H →L[ℂ] K) (A : TraceClass H) :
    IsTraceClass (operatorConjugation V A.1) := by
  let F := (operatorConjugation V).comp inclusionCLM
  have hpositive (B : TraceClass H) (hB : 0 ≤ B.1) : IsTraceClass (F B) :=
    isTraceClass_operatorConjugation_of_nonneg V B hB
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) : IsTraceClass (F B) := by
    rw [← TraceClass.positivePart_sub_negativePart B hB, map_sub]
    simpa only [sub_eq_add_neg] using isTraceClass_add
      (hpositive _ (TraceClass.positivePart_nonneg B hB))
      (isTraceClass_neg (hpositive _ (TraceClass.negativePart_nonneg B hB)))
  change IsTraceClass (F A)
  rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A, map_add, map_smul]
  exact isTraceClass_add (hself _ (TraceClass.realComponent_isSelfAdjoint A))
    (isTraceClass_smul Complex.I (hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)))

/-- Actual rectangular conjugation as a complex-linear trace-class map. -/
def conjugationLinearMap (V : H →L[ℂ] K) : TraceClass H →ₗ[ℂ] TraceClass K where
  toFun A := TraceClass.ofOperator (operatorConjugation V A.1)
    (isTraceClass_operatorConjugation V A)
  map_add' A B := Subtype.ext (((operatorConjugation V).comp inclusionCLM).map_add A B)
  map_smul' c A := Subtype.ext (((operatorConjugation V).comp inclusionCLM).map_smul c A)

@[simp] lemma conjugationLinearMap_coe (V : H →L[ℂ] K) (A : TraceClass H) :
    (conjugationLinearMap V A).1 = operatorConjugation V A.1 := rfl

lemma conjugationLinearMap_vectorProjector (V : H →L[ℂ] K) (x : H) :
    conjugationLinearMap V (vectorProjector x) = vectorProjector (V x) :=
  Subtype.ext (operatorConjugation_rankOne V x)

lemma conjugationLinearMap_positive_hasSum (V : H →L[ℂ] K)
    (A : TraceClass H) (hA : 0 ≤ A.1) {w : Set H} (b : HilbertBasis w ℂ H) :
    HasSum (fun i : w => vectorProjector (V (CFC.sqrt A.1 (b i))))
      (conjugationLinearMap V A) := by
  have heq : (∑' i : w, vectorProjector (V (CFC.sqrt A.1 (b i)))) =
      conjugationLinearMap V A :=
    Subtype.ext (conjugated_positive_vectors_tsum_coe V A hA b)
  exact heq ▸ (summable_conjugated_positive_vectors V A hA b).hasSum

lemma conjugationLinearMap_nonneg (V : H →L[ℂ] K) (A : TraceClass H) (hA : 0 ≤ A.1) :
    0 ≤ (conjugationLinearMap V A).1 := operatorConjugation_nonneg V A.1 hA

lemma conjugationLinearMap_completelyPositive (V : H →L[ℂ] K) :
    IsCompletelyPositive (conjugationLinearMap V) := by
  intro n A hA x
  convert hA (fun i => V.adjoint (x i)) using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, V ((A i j).1 (V.adjoint (x j)))⟫_ℂ = _
  exact (V.adjoint_inner_left ((A i j).1 (V.adjoint (x j))) (x i)).symm

lemma conjugationLinearMap_isometry_trace_of_nonneg (V : H →ₗᵢ[ℂ] K)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    traceCLM (conjugationLinearMap V.toContinuousLinearMap A) = traceCLM A := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hleft := (conjugationLinearMap_positive_hasSum V.toContinuousLinearMap A hA b).mapL traceCLM
  have hright := (positive_rankOne_series hA A.2 b).mapL traceCLM
  have hleft' : HasSum (fun i : w => traceCLM (vectorProjector (CFC.sqrt A.1 (b i))))
      (traceCLM (conjugationLinearMap V.toContinuousLinearMap A)) := by
    simpa only [traceCLM_vectorProjector, LinearIsometry.coe_toContinuousLinearMap, V.norm_map]
      using hleft
  exact hleft'.unique hright

/-- Isometric rectangular conjugation preserves the actual complex trace on
all trace-class inputs. -/
theorem conjugationLinearMap_isometry_trace (V : H →ₗᵢ[ℂ] K) (A : TraceClass H) :
    traceCLM (conjugationLinearMap V.toContinuousLinearMap A) = traceCLM A := by
  let D : TraceClass H →ₗ[ℂ] ℂ :=
    traceCLM.toLinearMap.comp (conjugationLinearMap V.toContinuousLinearMap) - traceCLM.toLinearMap
  have hpos (B : TraceClass H) (hB : 0 ≤ B.1) : D B = 0 :=
    sub_eq_zero.mpr (conjugationLinearMap_isometry_trace_of_nonneg V B hB)
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) : D B = 0 := by
    rw [← TraceClass.positivePart_sub_negativePart B hB, map_sub,
      hpos _ (TraceClass.positivePart_nonneg B hB),
      hpos _ (TraceClass.negativePart_nonneg B hB), sub_self]
  have hz : D A = 0 := by
    rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A, map_add, map_smul,
      hself _ (TraceClass.realComponent_isSelfAdjoint A),
      hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)]
    simp
  exact sub_eq_zero.mp hz

/-- The genuine CPTP pushforward by an isometry between different Hilbert spaces. -/
def QuantumChannel.ofIsometry (V : H →ₗᵢ[ℂ] K) : QuantumChannel H K where
  toLinearMap := conjugationLinearMap V.toContinuousLinearMap
  map_nonneg := conjugationLinearMap_nonneg V.toContinuousLinearMap
  trace_preserving := conjugationLinearMap_isometry_trace V
  completelyPositive := conjugationLinearMap_completelyPositive V.toContinuousLinearMap

@[simp] lemma QuantumChannel.ofIsometry_apply_coe (V : H →ₗᵢ[ℂ] K) (A : TraceClass H) (x : K) :
    ((QuantumChannel.ofIsometry V).toLinearMap A).1 x =
      V (A.1 (V.toContinuousLinearMap.adjoint x)) := rfl

lemma QuantumChannel.ofIsometry_vectorProjector (V : H →ₗᵢ[ℂ] K) (x : H) :
    (QuantumChannel.ofIsometry V).toLinearMap (vectorProjector x) = vectorProjector (V x) :=
  conjugationLinearMap_vectorProjector V.toContinuousLinearMap x

end
end Cloning.InfiniteTraceClass
