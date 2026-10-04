import Cloning.InfiniteCompletelyPositive

/-!
# Completely positive repair of trace loss

A positive scalar functional gives a completely positive replacement map on
the actual trace-class spaces. Applied to the trace deficit of a completely
positive, trace-nonincreasing map, this constructs an actual quantum channel.
No complete-positivity witness for the repair is assumed.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace BigOperators

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι]

/-- Scalar compression shows that every positive linear functional is
completely positive, at the level of its scalar-valued block matrices. -/
theorem BlockPositive.functionalMatrix {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (f : TraceClass H →ₗ[ℂ] ℂ)
    (hf : ∀ T, 0 ≤ T.1 → 0 ≤ f T) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * c j * f (A i j) := by
  have h := hf (∑ i, ∑ j, (star (c i) * c j) • A i j) (hA.scalarCompression c)
  simpa only [map_sum, map_smul, smul_eq_mul] using h

theorem BlockPositive.replacePure_functional {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (f : TraceClass H →ₗ[ℂ] ℂ)
    (hf : ∀ T, 0 ≤ T.1 → 0 ≤ f T) (z : K) :
    BlockPositive (fun i j => f (A i j) • vectorProjector z) := by
  intro x
  convert hA.functionalMatrix f hf (fun i => ⟪z, x i⟫_ℂ) using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, (f (A i j) • InnerProductSpace.rankOne ℂ z z) (x j)⟫_ℂ = _
  simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right, ← inner_conj_symm (x i) z]
  simp only [starRingEnd_apply]
  ring

/-- Infinite-rank replacement is obtained from the convergent rank-one
expansion of the positive trace-class output operator. -/
theorem BlockPositive.replace_functional {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (f : TraceClass H →ₗ[ℂ] ℂ)
    (hf : ∀ T, 0 ≤ T.1 → 0 ≤ f T) (σ : TraceClass K) (hσ : 0 ≤ σ.1) :
    BlockPositive (fun i j => f (A i j) • σ) := by
  intro x
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  let E := replacementExpectation (fun i j => f (A i j)) x
  have hs := (positive_rankOne_series hσ σ.2 b).mapL E
  have hnonneg : ∀ k : w, 0 ≤ E (vectorProjector (CFC.sqrt σ.1 (b k))) := by
    intro k
    have h := hA.replacePure_functional f hf (CFC.sqrt σ.1 (b k)) x
    change 0 ≤ replacementExpectation (fun i j => f (A i j)) x _
    rw [replacementExpectation_apply]
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change _ = ⟪x i, (f (A i j) •
      (vectorProjector (CFC.sqrt σ.1 (b k))).1) (x j)⟫_ℂ
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  have hsum : 0 ≤ E (TraceClass.ofOperator σ.1 σ.2) := by
    rw [← hs.tsum_eq]
    exact tsum_nonneg hnonneg
  change 0 ≤ E σ at hsum
  rw [replacementExpectation_apply] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, (f (A i j) • σ.1) (x j)⟫_ℂ = _
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

theorem functionalReplacement_completelyPositive (f : TraceClass H →ₗ[ℂ] ℂ)
    (hf : ∀ T, 0 ≤ T.1 → 0 ≤ f T) (σ : TraceClass K) (hσ : 0 ≤ σ.1) :
    IsCompletelyPositive (f.smulRight σ) := by
  intro n A hA
  exact hA.replace_functional f hf σ hσ

/-- Ordinary positivity follows from complete positivity at ancilla dimension one. -/
theorem IsCompletelyPositive.map_nonneg {Φ : TraceClass H →ₗ[ℂ] TraceClass K}
    (hΦ : IsCompletelyPositive Φ) (A : TraceClass H) (hA : 0 ≤ A.1) :
    0 ≤ (Φ A).1 := by
  have hblock : BlockPositive (fun _ _ : Fin 1 => A) := by
    intro x
    simpa only [Fin.sum_univ_one] using
      (A.1.nonneg_iff_isPositive.mp hA).inner_nonneg_right (x 0)
  apply nonneg_of_inner_nonneg
  intro y
  simpa only [Fin.sum_univ_one] using hΦ 1 _ hblock (fun _ => y)

theorem IsCompletelyPositive.add {Φ Ψ : TraceClass H →ₗ[ℂ] TraceClass K}
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Φ + Ψ) := by
  intro n A hA x
  have h := add_nonneg (hΦ n A hA x) (hΨ n A hA x)
  convert h using 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, ((Φ (A i j)).1 + (Ψ (A i j)).1) (x j)⟫_ℂ = _
  simp only [ContinuousLinearMap.add_apply, inner_add_right]

/-- The complex-linear trace deficit, defined on all inputs. -/
def traceDefect (Φ : TraceClass H →ₗ[ℂ] TraceClass K) : TraceClass H →ₗ[ℂ] ℂ :=
  traceCLM.toLinearMap - traceCLM.toLinearMap.comp Φ

@[simp] theorem traceDefect_apply (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (A : TraceClass H) : traceDefect Φ A = traceCLM A - traceCLM (Φ A) := rfl

theorem traceDefect_nonneg {Φ : TraceClass H →ₗ[ℂ] TraceClass K}
    (hΦ : IsCompletelyPositive Φ)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ (traceCLM A).re)
    (A : TraceClass H) (hA : 0 ≤ A.1) : 0 ≤ traceDefect Φ A := by
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa only [traceDefect_apply, Complex.sub_re] using sub_nonneg.mpr (htrace A hA)
  · simp only [traceDefect_apply, Complex.sub_im, traceCLM_apply,
      trace_im_eq_zero hA A.2, trace_im_eq_zero (hΦ.map_nonneg A hA) (Φ A).2,
      sub_self]

/-- Repair replaces precisely the missing trace in a fixed density state. -/
def traceRepairLinear (Φ : TraceClass H →ₗ[ℂ] TraceClass K) (σ : DensityState K) :
    TraceClass H →ₗ[ℂ] TraceClass K :=
  Φ + (traceDefect Φ).smulRight (TraceClass.ofOperator σ.op σ.traceClass)

@[simp] theorem traceRepairLinear_apply (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (σ : DensityState K) (A : TraceClass H) :
    traceRepairLinear Φ σ A = Φ A + (traceCLM A - traceCLM (Φ A)) •
      TraceClass.ofOperator σ.op σ.traceClass := rfl

theorem traceRepair_completelyPositive {Φ : TraceClass H →ₗ[ℂ] TraceClass K}
    (hΦ : IsCompletelyPositive Φ)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ (traceCLM A).re)
    (σ : DensityState K) : IsCompletelyPositive (traceRepairLinear Φ σ) :=
  hΦ.add (functionalReplacement_completelyPositive (traceDefect Φ)
    (traceDefect_nonneg hΦ htrace) _ σ.positive)

theorem traceRepair_trace_preserving (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (σ : DensityState K) (A : TraceClass H) :
    traceCLM (traceRepairLinear Φ σ A) = traceCLM A := by
  rw [traceRepairLinear_apply, map_add, map_smul]
  have hσ : traceCLM (TraceClass.ofOperator σ.op σ.traceClass) = 1 := σ.trace_one
  rw [hσ, smul_eq_mul, mul_one]
  ring

/-- A concrete CPTP completion of every CP trace-nonincreasing map. -/
def QuantumChannel.traceRepair (Φ : TraceClass H →ₗ[ℂ] TraceClass K)
    (hΦ : IsCompletelyPositive Φ)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ (traceCLM A).re)
    (σ : DensityState K) : QuantumChannel H K where
  toLinearMap := traceRepairLinear Φ σ
  map_nonneg := (traceRepair_completelyPositive hΦ htrace σ).map_nonneg
  trace_preserving := traceRepair_trace_preserving Φ σ
  completelyPositive := traceRepair_completelyPositive hΦ htrace σ

/-- Repair increases the image of every positive input in operator order. -/
theorem le_traceRepair_of_nonneg {Φ : TraceClass H →ₗ[ℂ] TraceClass K}
    (hΦ : IsCompletelyPositive Φ)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ (traceCLM A).re)
    (σ : DensityState K) (A : TraceClass H) (hA : 0 ≤ A.1) :
    (Φ A).1 ≤ (traceRepairLinear Φ σ A).1 := by
  change (Φ A).1 ≤ (Φ A).1 + traceDefect Φ A • σ.op
  exact le_add_of_nonneg_right (smul_nonneg (traceDefect_nonneg hΦ htrace A hA) σ.positive)

/-- The exact trace-norm cost of repair is the lost trace. -/
theorem norm_traceRepair_sub {Φ : TraceClass H →ₗ[ℂ] TraceClass K}
    (hΦ : IsCompletelyPositive Φ)
    (htrace : ∀ A, 0 ≤ A.1 → (traceCLM (Φ A)).re ≤ (traceCLM A).re)
    (σ : DensityState K) (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖traceRepairLinear Φ σ A - Φ A‖ = (traceCLM A).re - (traceCLM (Φ A)).re := by
  have hσnorm : ‖TraceClass.ofOperator σ.op σ.traceClass‖ = 1 := by
    rw [TraceClass.norm_eq_trace_re_of_nonneg _ σ.positive]
    change (trace σ.op σ.traceClass).re = 1
    rw [σ.trace_one]
    rfl
  have hdef : ‖traceDefect Φ A‖ = (traceDefect Φ A).re :=
    (Complex.re_eq_norm.mpr (traceDefect_nonneg hΦ htrace A hA)).symm
  change ‖(Φ A + traceDefect Φ A • TraceClass.ofOperator σ.op σ.traceClass) - Φ A‖ = _
  rw [add_sub_cancel_left, norm_smul, hσnorm, mul_one, hdef, traceDefect_apply,
    Complex.sub_re]

end
end Cloning.InfiniteTraceClass
