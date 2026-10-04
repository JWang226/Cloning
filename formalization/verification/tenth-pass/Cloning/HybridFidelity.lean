import Cloning.HybridStates
import Cloning.HybridIntegralBounds
import Cloning.InfiniteChannelFidelity

/-!
# Fidelity and trace-norm continuity for continuous classical–quantum states

The integral is the actual pointwise quantum root fidelity. Its measurability,
integrability, trace bound, data processing and dimension-independent continuity
are proved for positive trace-class-valued `L¹` fields on arbitrary measure spaces.
-/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid.PositiveField
set_option backward.isDefEq.respectTransparency false
variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma integrable_rootFidelity (R S : PositiveField (H := H) μ) :
    Integrable (fun x => PositiveTraceClass.rootFidelity (R.value x) (S.value x)) μ := by
  apply (integrable_sqrt_mul_sqrt R.integrable.norm S.integrable.norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mono'
    (PositiveTraceClass.continuous_rootFidelity.comp_aestronglyMeasurable
      (R.measurable.prodMk S.measurable))
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (PositiveTraceClass.rootFidelity_nonneg _ _)]
    exact PositiveTraceClass.rootFidelity_le_sqrt _ _

/-- Root fidelity for a continuous classical–quantum register. -/
def rootFidelity (R S : PositiveField (H := H) μ) : ℝ :=
  ∫ x, PositiveTraceClass.rootFidelity (R.value x) (S.value x) ∂μ

lemma rootFidelity_nonneg (R S : PositiveField (H := H) μ) : 0 ≤ R.rootFidelity S :=
  integral_nonneg (fun x => PositiveTraceClass.rootFidelity_nonneg _ _)

lemma rootFidelity_comm (R S : PositiveField (H := H) μ) : R.rootFidelity S = S.rootFidelity R := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x => PositiveTraceClass.rootFidelity_comm _ _

@[simp] lemma rootFidelity_self (R : PositiveField (H := H) μ) : R.rootFidelity R = R.mass := by
  simp only [rootFidelity, PositiveTraceClass.rootFidelity_self, mass]

/-- The fidelity of arbitrary positive integrable fields is bounded by their
integrated trace masses; pointwise normalization is unnecessary. -/
theorem rootFidelity_le_sqrt_mass (R S : PositiveField (H := H) μ) :
    R.rootFidelity S ≤ Real.sqrt R.mass * Real.sqrt S.mass := by
  calc
    R.rootFidelity S ≤ ∫ x, Real.sqrt ‖(R.value x).1‖ * Real.sqrt ‖(S.value x).1‖ ∂μ :=
      integral_mono (R.integrable_rootFidelity S)
        (integrable_sqrt_mul_sqrt R.integrable.norm S.integrable.norm
          (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
        (fun x => PositiveTraceClass.rootFidelity_le_sqrt _ _)
    _ ≤ _ := integral_sqrt_mul_sqrt_le R.integrable.norm S.integrable.norm
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

lemma rootFidelity_le_one (R S : PositiveField (H := H) μ)
    (hR : R.mass ≤ 1) (hS : S.mass ≤ 1) : R.rootFidelity S ≤ 1 := by
  have h := R.rootFidelity_le_sqrt_mass S
  have hR' : Real.sqrt R.mass ≤ 1 := (Real.sqrt_le_one).mpr hR
  have hS' : Real.sqrt S.mass ≤ 1 := (Real.sqrt_le_one).mpr hS
  exact h.trans (by nlinarith [Real.sqrt_nonneg R.mass, Real.sqrt_nonneg S.mass])

/-- The full continuity bound for unnormalized hybrid states. The norm is the
integral of the fibre trace norm, as required by the continuous-register LAN model. -/
theorem rootFidelity_continuity (R S T U : PositiveField (H := H) μ) :
    |R.rootFidelity S - T.rootFidelity U| ≤
      Real.sqrt (R.traceDistance T) * Real.sqrt S.mass +
      Real.sqrt (S.traceDistance U) * Real.sqrt T.mass := by
  have hi₁ := integrable_sqrt_mul_sqrt (R.integrable.sub T.integrable).norm S.integrable.norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hi₂ := integrable_sqrt_mul_sqrt (S.integrable.sub U.integrable).norm T.integrable.norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  calc
    |R.rootFidelity S - T.rootFidelity U| =
        |∫ x, (PositiveTraceClass.rootFidelity (R.value x) (S.value x) -
          PositiveTraceClass.rootFidelity (T.value x) (U.value x)) ∂μ| := by
      rw [integral_sub (R.integrable_rootFidelity S) (T.integrable_rootFidelity U)]
      rfl
    _ ≤ ∫ x, |PositiveTraceClass.rootFidelity (R.value x) (S.value x) -
          PositiveTraceClass.rootFidelity (T.value x) (U.value x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (Real.sqrt ‖(R.value x).1 - (T.value x).1‖ * Real.sqrt ‖(S.value x).1‖ +
        Real.sqrt ‖(S.value x).1 - (U.value x).1‖ * Real.sqrt ‖(T.value x).1‖) ∂μ := by
      apply integral_mono
        ((R.integrable_rootFidelity S).sub (T.integrable_rootFidelity U)).abs (hi₁.add hi₂)
      intro x
      exact PositiveTraceClass.rootFidelity_continuity _ _ _ _
    _ = (∫ x, Real.sqrt ‖(R.value x).1 - (T.value x).1‖ * Real.sqrt ‖(S.value x).1‖ ∂μ) +
        (∫ x, Real.sqrt ‖(S.value x).1 - (U.value x).1‖ * Real.sqrt ‖(T.value x).1‖ ∂μ) :=
      integral_add hi₁ hi₂
    _ ≤ _ := add_le_add
      (integral_sqrt_mul_sqrt_le (R.integrable.sub T.integrable).norm S.integrable.norm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      (integral_sqrt_mul_sqrt_le (S.integrable.sub U.integrable).norm T.integrable.norm
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))

/-- The normalized continuity modulus is independent of both the classical
register and the quantum Hilbert-space dimension. -/
theorem rootFidelity_continuity_subnormalized (R S T U : PositiveField (H := H) μ)
    (hS : S.mass ≤ 1) (hT : T.mass ≤ 1) :
    |R.rootFidelity S - T.rootFidelity U| ≤
      Real.sqrt (R.traceDistance T) + Real.sqrt (S.traceDistance U) := by
  apply (rootFidelity_continuity R S T U).trans
  exact add_le_add
    (by
      simpa using mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hS)
        (Real.sqrt_nonneg (R.traceDistance T)))
    (by
      simpa using mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hT)
        (Real.sqrt_nonneg (S.traceDistance U)))

/-- Complete positivity in every fibre implies hybrid fidelity data processing. -/
theorem rootFidelity_map_le (Φ : QuantumChannel H K) (R S : PositiveField (H := H) μ) :
    R.rootFidelity S ≤ (R.map Φ.toPositiveTracePreservingMap).rootFidelity
      (S.map Φ.toPositiveTracePreservingMap) := by
  apply integral_mono (R.integrable_rootFidelity S)
    ((R.map Φ.toPositiveTracePreservingMap).integrable_rootFidelity
      (S.map Φ.toPositiveTracePreservingMap))
  intro x
  exact fidelity_data_processing Φ (R.value x).1 (S.value x).1 (R.value x).2 (S.value x).2

/-- Almost-everywhere equality of representatives preserves the hybrid fidelity. -/
theorem rootFidelity_congr_ae {R S T U : PositiveField (H := H) μ}
    (hRT : R.value =ᵐ[μ] T.value) (hSU : S.value =ᵐ[μ] U.value) :
    R.rootFidelity S = T.rootFidelity U := by
  apply integral_congr_ae
  filter_upwards [hRT, hSU] with x hR hS
  rw [hR, hS]

end Cloning.Hybrid.PositiveField
