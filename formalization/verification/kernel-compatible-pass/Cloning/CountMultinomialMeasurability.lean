import Cloning.CountMultinomialDensity
import Cloning.YoungUniformLocalQuantization

/-! Continuous parameter dependence and joint measurability of actual count smoothing. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory TopologicalSpace
namespace Cloning.CountMultinomial
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.GeneralSymmetricOccupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem density_eq_lattice (d N : ℕ) (hN : 0<N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1) (x : rootSpace d) :
    density d N p hp hs x=(Real.sqrt (N : ℝ)^d/Real.sqrt ((d : ℝ)+1))*
      (latticePMF d N p hp hs (sampleLabel d N (flatSpectrum (d+1)) x)).toReal := by
  rw [density, sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) _ _ _ x
    (mem_sampleCell_sampleLabel d N (flatSpectrum (d+1)) x)]
  norm_cast

theorem density_eq_word_sum (d N : ℕ) (hN : 0<N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1) (x : rootSpace d) :
    density d N p hp hs x=(Real.sqrt (N : ℝ)^d/Real.sqrt ((d : ℝ)+1))*
      (∑ w : Word N (d+1), if sampleLabel d N (flatSpectrum (d+1)) x=shapeLattice d N (countShape w)
        then wordWeight p w else 0) := by
  rw [density_eq_lattice d N hN, latticePMF, countPMF, PMF.map_comp, PMF.map_apply,
    tsum_fintype, ENNReal.toReal_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [Function.comp_def]
    split_ifs
    · exact wordPMF_toReal _ _ _ _ _ _
    · rfl
  · intro w _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top

theorem measurable_density (d N : ℕ) (hN : 0<N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1) : Measurable (density d N p hp hs) := by
  change Measurable (fun x ↦ density d N p hp hs x)
  simp_rw [density_eq_lattice d N hN]
  exact ((measurable_of_countable (fun μ : Lattice d (N : ℤ) ↦
    (latticePMF d N p hp hs μ).toReal)).comp (measurable_sampleLabel d N _)).const_mul _

theorem continuous_density_parameter {Z : Type*} [TopologicalSpace Z]
    (d N : ℕ) (hN : 0<N) (p : Z → Fin (d+1) → ℝ)
    (hp : ∀ z i, 0≤p z i) (hs : ∀ z, ∑ i, p z i=1)
    (hc : ∀ i, Continuous (fun z ↦ p z i)) (x : rootSpace d) :
    Continuous (fun z ↦ density d N (p z) (hp z) (hs z) x) := by
  simp_rw [density_eq_word_sum d N hN]
  apply Continuous.const_mul
  apply continuous_finset_sum
  intro w _
  by_cases hw : sampleLabel d N (flatSpectrum (d+1)) x=shapeLattice d N (countShape w)
  · simp only [hw, if_true, wordWeight]
    exact continuous_finset_prod _ (fun i _ ↦ hc (w i))
  · simp only [hw, if_false]
    exact continuous_const

theorem measurable_density_uncurry {Z : Type*} [TopologicalSpace Z] [MetrizableSpace Z]
    [MeasurableSpace Z] [SecondCountableTopology Z] [OpensMeasurableSpace Z]
    (d N : ℕ) (hN : 0<N) (p : Z → Fin (d+1) → ℝ)
    (hp : ∀ z i, 0≤p z i) (hs : ∀ z, ∑ i, p z i=1)
    (hc : ∀ i, Continuous (fun z ↦ p z i)) :
    Measurable (fun zx : Z×rootSpace d ↦ density d N (p zx.1) (hp zx.1) (hs zx.1) zx.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (continuous_density_parameter d N hN p hp hs hc) (fun z ↦ measurable_density d N hN (p z) (hp z) (hs z))

end Cloning.CountMultinomial
