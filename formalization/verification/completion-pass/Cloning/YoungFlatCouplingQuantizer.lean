import Cloning.YoungFlatCouplingDensity
import Cloning.YoungFlatSmoothing

/-! Exact recovery of the finite physical Young law by the clamped shape
quantizer. Invalid finite shapes carry zero physical probability. -/
noncomputable section
open scoped BigOperators Topology Classical ENNReal
open MeasureTheory Filter
namespace Cloning.YoungFlatCoupling
open Cloning.YoungHyperplane Cloning.YoungGeneral Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def shapeOfLattice (d N : ℕ) (z : Lattice d (N : ℤ)) : Shape (d+1) N :=
  fun i => ⟨min (z.1 i).toNat N, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem shapeOfLattice_shapeLattice (d N : ℕ) (s : Shape (d+1) N)
    (hs : ∑ i, (s i).val = N) : shapeOfLattice d N (shapeLattice d N s) = s := by
  funext i
  apply Fin.ext
  change min ((shapeLattice d N s).1 i).toNat N = (s i).val
  rw [shapeLattice_apply d N s hs, Int.toNat_natCast, min_eq_left (Nat.le_of_lt_succ (s i).isLt)]

theorem map_shapeOfLattice_tensorYoungLatticePMF (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (tensorYoungLatticePMF d N p hp hs).map (shapeOfLattice d N) =
      tensorYoungPMF N (d+1) p hp hs := by
  rw [tensorYoungLatticePMF, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id (tensorYoungPMF N (d+1) p hp hs)]
  ext s
  simp only [PMF.map_apply]
  apply tsum_congr
  intro z
  by_cases hz : ∑ i, (z i).val = N
  · simp only [Function.comp_apply, shapeOfLattice_shapeLattice d N z hz, id_eq]
    split_ifs <;> rfl
  · have he : tensorYoungPMF N (d+1) p hp hs z = 0 :=
      physicalYoungPMF_eq_zero_of_not_partition _ _ _ _ _ _ z (Or.inr hz)
    simp only [he, ite_self]

theorem measurable_sampleShape (d N : ℕ) (p : Fin (d+1) → ℝ) :
    Measurable (sampleShape d N p) :=
  (measurable_of_countable (shapeOfLattice d N)).comp (measurable_sampleLabel d N p)

theorem map_sampleShape_physicalSmoothedMeasure (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Measure.map (sampleShape d N p) (physicalSmoothedMeasure d N p hp hs) =
      (tensorYoungPMF N (d+1) p hp hs).toMeasure := by
  change Measure.map (shapeOfLattice d N ∘ sampleLabel d N p) _ = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_sampleLabel d N p),
    map_sampleLabel_physicalSmoothedMeasure d N hN p hp hs]
  exact (PMF.toMeasure_map (shapeOfLattice d N) (tensorYoungLatticePMF d N p hp hs)
    (measurable_of_countable _)).trans (congrArg PMF.toMeasure
      (map_shapeOfLattice_tensorYoungLatticePMF d N p hp hs))

theorem densityBin_sampleShape (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (s : Shape (d+1) N) :
    densityBin volume (sampleShape d N p) (tensorYoungDensity d N p hp hs) s =
      (tensorYoungPMF N (d+1) p hp hs s).toReal := by
  have he := congrArg (fun μ : Measure (Shape (d+1) N) => μ {s})
    (map_sampleShape_physicalSmoothedMeasure d N hN p hp hs)
  dsimp only at he
  rw [Measure.map_apply (measurable_sampleShape d N p) (measurableSet_singleton s),
    physicalSmoothedMeasure_apply d N hN p hp hs _
      ((measurable_sampleShape d N p) (measurableSet_singleton s)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)] at he
  have hn := densityBin_nonneg volume (sampleShape d N p) _
    (tensorYoungDensity_nonneg d N p hp hs) s
  have hi : densityBin volume (sampleShape d N p) (tensorYoungDensity d N p hp hs) s =
      ∫ x in (sampleShape d N p) ⁻¹' {s}, tensorYoungDensity d N p hp hs x := by
    rw [densityBin, ← integral_indicator ((measurable_sampleShape d N p) (measurableSet_singleton s))]
    rfl
  rw [← hi] at he
  exact (ENNReal.toReal_ofReal hn).symm.trans (congrArg ENNReal.toReal he)

end Cloning.YoungFlatCoupling
