import Cloning.YoungFlatSmoothing
import Cloning.TensorFlatProjectorCasimirMoment

/-! The sharp physical Casimir moment controls the actual smoothed flat laws. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlat
open Cloning.TensorLie Cloning.YoungHyperplane Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def smoothedMeasure (d N : ℕ) : Measure (rootSpace d) :=
  physicalSmoothedMeasure d N (flatSpectrum (d+1))
    (fun _ ↦ by unfold flatSpectrum; positivity) (flatSpectrum_sum _ (by omega))

def cellCenter (d N : ℕ) (x : rootSpace d) : rootSpace d :=
  sampleCenter d N (flatSpectrum (d+1)) (sampleLabel d N (flatSpectrum (d+1)) x)

theorem integrable_lattice_observable (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (f : Lattice d (N : ℤ) → ℝ) :
    Integrable f (tensorYoungLatticePMF d N p hp hs).toMeasure := by
  rw [tensorYoungLatticePMF, ← PMF.toMeasure_map (shapeLattice d N) (tensorYoungPMF N (d+1) p hp hs) (measurable_of_countable (shapeLattice d N))]
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mpr Integrable.of_finite

theorem integral_lattice_observable (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (f : Lattice d (N : ℤ) → ℝ) :
    (∫ μ, f μ ∂(tensorYoungLatticePMF d N p hp hs).toMeasure) =
      ∑ μ : Shape (d+1) N, (tensorYoungPMF N (d+1) p hp hs μ).toReal * f (shapeLattice d N μ) := by
  rw [tensorYoungLatticePMF, ← PMF.toMeasure_map (shapeLattice d N) (tensorYoungPMF N (d+1) p hp hs) (measurable_of_countable (shapeLattice d N)),
    integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    PMF.integral_eq_sum]
  rfl

theorem sampleCenter_flat_norm_sq (d N : ℕ) (hN : 0 < N) (μ : Shape (d+1) N)
    (hs : ∑ i, (μ i).val = N) :
    ‖sampleCenter d N (flatSpectrum (d+1)) (shapeLattice d N μ)‖^2 =
      (∑ i, (((μ i).val : ℝ)-(N : ℝ)/((d+1 : ℕ) : ℝ))^2)/(N : ℝ) := by
  change ‖(sampleCenter d N (flatSpectrum (d+1)) (shapeLattice d N μ)).1‖^2 = _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [sampleCenter_apply d N _ (flatSpectrum_sum _ (by omega)),
    shapeLattice_apply d N μ hs, Int.cast_natCast, flatSpectrum, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), mul_one_div]
  rw [Finset.sum_div]

/-- Integrability of the rounded-center moment uses finite physical label support. -/
theorem integrable_cellCenter_norm_sq (d N : ℕ) (hN : 0 < N) :
    Integrable (fun x ↦ ‖cellCenter d N x‖^2) (smoothedMeasure d N) := by
  let p := flatSpectrum (d+1)
  let hp : ∀ i, 0 ≤ p i := fun _ ↦ by dsimp [p, flatSpectrum]; positivity
  let hs := flatSpectrum_sum (d+1) (by omega)
  have hi := integrable_lattice_observable d N p hp hs
    (fun μ ↦ ‖sampleCenter d N p μ‖^2)
  rw [← map_sampleLabel_physicalSmoothedMeasure d N hN p hp hs] at hi
  exact hi.comp_aemeasurable (measurable_sampleLabel d N p).aemeasurable

/-- The exact physical Casimir estimate survives quantization without error. -/
theorem integral_cellCenter_norm_sq_le (d N : ℕ) (hN : 0 < N) :
    (∫ x, ‖cellCenter d N x‖^2 ∂smoothedMeasure d N) ≤ ((d+1 : ℕ) : ℝ) := by
  let p := flatSpectrum (d+1)
  let hp : ∀ i, 0 ≤ p i := fun _ ↦ by dsimp [p, flatSpectrum]; positivity
  let hs := flatSpectrum_sum (d+1) (by omega)
  change (∫ x, ‖sampleCenter d N p (sampleLabel d N p x)‖^2
    ∂physicalSmoothedMeasure d N p hp hs) ≤ _
  rw [integral_sampleLabel_physicalSmoothedMeasure d N hN p hp hs
    (fun μ : Lattice d (N : ℤ) ↦ ‖sampleCenter d N p μ‖^2),
    integral_lattice_observable d N p hp hs
      (fun μ : Lattice d (N : ℤ) ↦ ‖sampleCenter d N p μ‖^2)]
  have he : (∑ μ : Shape (d+1) N, (tensorYoungPMF N (d+1) p hp hs μ).toReal *
      ‖sampleCenter d N p (shapeLattice d N μ)‖^2) =
      (∑ μ : Shape (d+1) N, (tensorFlatYoungPMF N (d+1) (by omega) μ).toReal *
        (∑ i, (((μ i).val : ℝ)-(N : ℝ)/((d+1 : ℕ) : ℝ))^2))/(N : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro μ _
    by_cases hsum : ∑ i, (μ i).val = N
    · rw [sampleCenter_flat_norm_sq d N hN μ hsum]
      exact (mul_div_assoc _ _ _).symm
    · have hz : tensorYoungPMF N (d+1) p hp hs μ = 0 :=
        physicalYoungPMF_eq_zero_of_not_partition _ _ _ _ _ _ μ (Or.inr hsum)
      change (tensorYoungPMF N (d+1) p hp hs μ).toReal * _ =
        ((tensorYoungPMF N (d+1) p hp hs μ).toReal * _)/(N : ℝ)
      simp [hz]
  rw [he]
  have hm := tensorFlatYoungPMF_centered_second_moment_le (n := N) (by omega : 0<d+1)
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hnR).mpr
  have hr : (0 : ℝ) ≤ 1/((d+1 : ℕ) : ℝ) := by positivity
  nlinarith

end Cloning.YoungFlat
