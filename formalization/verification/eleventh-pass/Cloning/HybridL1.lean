import Cloning.HybridFidelity
import Cloning.ChannelAveraging
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# The actual operator-valued L¹ space behind hybrid states

Positive fields map to Mathlib's Banach space of integrable functions modulo
almost-everywhere equality. Their mass and trace distance agree exactly with
the `L¹` norm. Forgetting the continuous classical register produces a positive
trace-class operator, and its trace is the integrated trace.
-/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid.PositiveField
set_option backward.isDefEq.respectTransparency false
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine `L¹` equivalence class of an operator-valued density. -/
def toL1 (R : PositiveField (H := H) μ) : Lp (TraceClass H) 1 μ :=
  R.integrable.toL1 (fun x => (R.value x).1)

lemma coe_toL1 (R : PositiveField (H := H) μ) :
    R.toL1 =ᵐ[μ] (fun x => (R.value x).1) := R.integrable.coeFn_toL1

lemma norm_toL1 (R : PositiveField (H := H) μ) : ‖R.toL1‖ = R.mass := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (R.coe_toL1.fun_comp norm)

/-- Hybrid trace distance is exactly the norm difference in operator-valued L¹. -/
theorem traceDistance_eq_norm (R S : PositiveField (H := H) μ) :
    R.traceDistance S = ‖R.toL1 - S.toL1‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub R.toL1 S.toL1, R.coe_toL1, S.coe_toL1] with x hsub hR hS
  dsimp only [Pi.sub_apply] at hsub
  rw [hsub, hR, hS]

lemma toL1_eq_iff (R S : PositiveField (H := H) μ) :
    R.toL1 = S.toL1 ↔ R.value =ᵐ[μ] S.value := by
  rw [toL1, toL1, Integrable.toL1_eq_toL1_iff]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact Subtype.ext hx
  · intro h
    filter_upwards [h] with x hx
    rw [hx]

lemma traceDistance_eq_zero_iff (R S : PositiveField (H := H) μ) :
    R.traceDistance S = 0 ↔ R.value =ᵐ[μ] S.value := by
  rw [traceDistance_eq_norm, norm_eq_zero, sub_eq_zero, toL1_eq_iff]

/-- Fidelity depends only on the two actual L¹ equivalence classes. -/
lemma rootFidelity_eq_of_toL1_eq {R S T U : PositiveField (H := H) μ}
    (hRT : R.toL1 = T.toL1) (hSU : S.toL1 = U.toL1) :
    R.rootFidelity S = T.rootFidelity U :=
  rootFidelity_congr_ae ((toL1_eq_iff R T).mp hRT) ((toL1_eq_iff S U).mp hSU)

/-- The operator-valued Bochner integral is a positive trace-class operator. -/
theorem quantumMarginal_nonneg (R : PositiveField (H := H) μ) :
    0 ≤ R.quantumMarginal.1 := by
  apply R.quantumMarginal.1.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex R.quantumMarginal.1).mpr
  intro v
  have hnonneg : 0 ≤ ⟪v, R.quantumMarginal.1 v⟫_ℂ := by
    have hi := (traceClassMatrixCoefficient v v).integrable_comp R.integrable
    have h := integral_complex_nonneg hi (fun x =>
      (((R.value x).1.1).nonneg_iff_isPositive.mp (R.value x).2).inner_nonneg_right v)
    have he := (traceClassMatrixCoefficient v v).integral_comp_comm R.integrable
    change (∫ x, ⟪v, (R.value x).1.1 v⟫_ℂ ∂μ) = ⟪v, R.quantumMarginal.1 v⟫_ℂ at he
    simp only [traceClassMatrixCoefficient_apply] at h
    rwa [he] at h
  have hleft : 0 ≤ ⟪R.quantumMarginal.1 v, v⟫_ℂ := by
    rw [← inner_conj_symm (R.quantumMarginal.1 v) v]
    apply Complex.nonneg_iff.mpr
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnonneg
    simpa only [Complex.conj_re, Complex.conj_im, ← him, neg_zero] using And.intro hre (rfl : (0 : ℝ) = 0)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hleft
  refine ⟨?_, hre⟩
  apply Complex.ext
  · simp
  · simpa using him

/-- A hybrid state of total trace one yields an actual quantum density state
by forgetting the classical register. -/
def marginalState (R : PositiveField (H := H) μ) (hR : R.mass = 1) : DensityState H where
  op := R.quantumMarginal.1
  positive := R.quantumMarginal_nonneg
  traceClass := R.quantumMarginal.2
  trace_one := by
    apply Complex.ext
    · exact R.trace_quantumMarginal.trans hR
    · exact trace_im_eq_zero R.quantumMarginal_nonneg R.quantumMarginal.2

/-- Forgetting the classical register contracts the actual trace distance. -/
theorem quantumMarginal_norm_sub_le (R S : PositiveField (H := H) μ) :
    ‖R.quantumMarginal - S.quantumMarginal‖ ≤ R.traceDistance S := by
  rw [quantumMarginal, quantumMarginal, ← integral_sub R.integrable S.integrable]
  exact norm_integral_le_integral_norm _

end Cloning.Hybrid.PositiveField
