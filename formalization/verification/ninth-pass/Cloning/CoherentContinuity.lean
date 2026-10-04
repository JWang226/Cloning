import Cloning.CoherentKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp

/-! Continuity and Bochner integrability of the actual complex coherent vectors
and their trace-class projectors. The proved overlap kernel supplies norm
continuity even at zero, where a separately chosen phase is discontinuous. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass

namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The actual complex coherent vector is continuous in its amplitude,
including at zero. -/
theorem continuous_coherentVector : Continuous coherentVector := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hn (w : ℂ) : ‖coherentVector w - coherentVector z‖ ^ 2 =
      2 - 2 * (⟪coherentVector w, coherentVector z⟫_ℂ).re := by
    have h := norm_sub_sq (𝕜 := ℂ) (coherentVector w) (coherentVector z)
    simp only [coherentVector_norm, one_pow] at h
    change ‖coherentVector w - coherentVector z‖ ^ 2 =
      1 - 2 * (⟪coherentVector w, coherentVector z⟫_ℂ).re + 1 at h
    linarith
  have hs : Continuous (fun w : ℂ => ‖coherentVector w - coherentVector z‖ ^ 2) := by
    simp_rw [hn, inner_coherentVector]
    fun_prop
  have ht : Tendsto (fun w : ℂ => ‖coherentVector w - coherentVector z‖ ^ 2)
      (𝓝 z) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hs.tendsto z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

/-- The rank-one coherent density as an element of the actual trace-class Banach space. -/
def coherentProjector (z : ℂ) : TraceClass Fock := vectorProjector (coherentVector z)

theorem continuous_coherentProjector : Continuous coherentProjector := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact vectorProjector_tendsto (continuous_coherentVector.tendsto z)

theorem coherentProjector_norm (z : ℂ) : ‖coherentProjector z‖ = 1 := by
  rw [coherentProjector, norm_vectorProjector, coherentVector_norm, one_pow]

theorem coherentProjector_trace (z : ℂ) : traceCLM (coherentProjector z) = 1 := by
  rw [coherentProjector, traceCLM_vectorProjector, coherentVector_norm, one_pow]
  rfl

theorem coherentProjector_nonneg (z : ℂ) : 0 ≤ (coherentProjector z).1 := by
  change 0 ≤ InnerProductSpace.rankOne ℂ (coherentVector z) (coherentVector z)
  exact (InnerProductSpace.rankOne ℂ _ _).nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self _)

/-- The normalized complex coherent vector also gives a bundled density state. -/
def coherentState (z : ℂ) : DensityState Fock :=
  DensityState.pure (coherentVector z) (coherentVector_norm z)

theorem stronglyMeasurable_coherentVector : StronglyMeasurable coherentVector :=
  continuous_coherentVector.stronglyMeasurable

theorem stronglyMeasurable_coherentProjector : StronglyMeasurable coherentProjector :=
  continuous_coherentProjector.stronglyMeasurable

/-- Unit norm gives Bochner integrability for every finite measure, including
all circular Gaussian probability laws used in thermal mixtures. -/
theorem integrable_coherentVector (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable coherentVector μ := by
  apply (integrable_const (1 : ℝ)).mono' continuous_coherentVector.aestronglyMeasurable
  exact Eventually.of_forall (fun z => le_of_eq (coherentVector_norm z))

/-- This is integrability in the genuine trace norm, with no assumed operator
integrability or measurability premise. -/
theorem integrable_coherentProjector (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable coherentProjector μ := by
  apply (integrable_const (1 : ℝ)).mono' continuous_coherentProjector.aestronglyMeasurable
  exact Eventually.of_forall (fun z => le_of_eq (coherentProjector_norm z))

end Cloning.ComplexCoherent
