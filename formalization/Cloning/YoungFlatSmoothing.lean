import Cloning.YoungFlatLocal
import Cloning.YoungUniformLocalQuantization
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Exact probability measures and label recovery for physical Young smoothing. -/
noncomputable section
open scoped BigOperators Topology Classical ENNReal
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def physicalSmoothedMeasure (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : Measure (rootSpace d) :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (tensorYoungDensity d N p hp hs x))

theorem physicalSmoothedMeasure_apply (d N : ℕ) (hN : 0 < N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (A : Set (rootSpace d)) (hA : MeasurableSet A) :
    physicalSmoothedMeasure d N p hp hs A =
      ENNReal.ofReal (∫ x in A, tensorYoungDensity d N p hp hs x) := by
  rw [physicalSmoothedMeasure, withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_tensorYoungDensity d N hN p hp hs).integrableOn
    (ae_of_all _ fun x ↦ tensorYoungDensity_nonneg d N p hp hs x)).symm

theorem physicalSmoothedMeasure_isProbability (d N : ℕ) (hN : 0 < N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    IsProbabilityMeasure (physicalSmoothedMeasure d N p hp hs) := by
  constructor
  rw [physicalSmoothedMeasure_apply d N hN p hp hs _ MeasurableSet.univ,
    setIntegral_univ, integral_tensorYoungDensity d N hN, ENNReal.ofReal_one]

/-- Quantization of the smoothed probability measure recovers exactly the actual physical law. -/
theorem map_sampleLabel_physicalSmoothedMeasure (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Measure.map (sampleLabel d N p) (physicalSmoothedMeasure d N p hp hs) =
      (tensorYoungLatticePMF d N p hp hs).toMeasure := by
  apply Measure.ext_of_singleton
  intro μ
  rw [Measure.map_apply (measurable_sampleLabel d N p) (measurableSet_singleton μ),
    physicalSmoothedMeasure_apply d N hN p hp hs _
      ((measurable_sampleLabel d N p) (measurableSet_singleton μ)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton μ)]
  change ENNReal.ofReal (YoungRounding.binMass volume (sampleLabel d N p)
    (tensorYoungDensity d N p hp hs) μ) = _
  rw [binMass_tensorYoungDensity d N hN p hp hs,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- Every lattice observable can be integrated using the exact physical measurement law. -/
theorem integral_sampleLabel_physicalSmoothedMeasure (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (f : Lattice d (N : ℤ) → ℝ) :
    (∫ x, f (sampleLabel d N p x) ∂physicalSmoothedMeasure d N p hp hs) =
      ∫ μ, f μ ∂(tensorYoungLatticePMF d N p hp hs).toMeasure := by
  rw [← map_sampleLabel_physicalSmoothedMeasure d N hN p hp hs]
  exact (integral_map (measurable_sampleLabel d N p).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

end Cloning.YoungHyperplane
