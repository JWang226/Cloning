import Cloning.CountMultinomialPMF
import Cloning.YoungFlatCells

/-! The true count law smoothed on fixed-base Euclidean root-space cells. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.CountMultinomial
open Cloning.YoungGeneral Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def latticePMF (d N : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    PMF (Lattice d (N : ℤ)) := (countPMF (d+1) N p hp hs).map (shapeLattice d N)

theorem latticePMF_apply_shape (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (μ : Shape (d+1) N)
    (hμ : ∑ i, (μ i).val=N) :
    latticePMF d N p hp hs (shapeLattice d N μ)=countPMF (d+1) N p hp hs μ := by
  rw [latticePMF, PMF.map_apply, tsum_eq_single μ]
  · simp
  · intro ν hν
    by_cases ht : ∑ i, (ν i).val=N
    · have hn : shapeLattice d N μ≠shapeLattice d N ν := by
        intro he
        exact hν (shapeLattice_injective_of_sum d N ν μ ht hμ he.symm)
      simp only [hn, if_false]
    · rw [countPMF_eq_zero_of_sum p hp hs ν ht]
      split_ifs <;> rfl

/-- Centering is fixed independently of the sampled probability vector. -/
def density (d N : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    rootSpace d → ℝ :=
  sampleInterpolate d N (flatSpectrum (d+1)) (fun μ ↦ (latticePMF d N p hp hs μ).toReal)

theorem density_eq_on_cell (d N : ℕ) (hN : 0<N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (μ : Shape (d+1) N) (hμ : ∑ i, (μ i).val=N)
    (x : rootSpace d) (hx : x∈sampleCell d N (flatSpectrum (d+1)) (shapeLattice d N μ)) :
    density d N p hp hs x=(Real.sqrt (N : ℝ)^d/Real.sqrt ((d : ℝ)+1))*
      YoungMultinomial.multinomialMass N p (fun i ↦ (μ i).val) := by
  rw [density, sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) _ _ _ x hx,
    latticePMF_apply_shape d N p hp hs μ hμ, countPMF_formula (d+1) N p hp hs μ hμ]
  norm_cast

theorem integral_density (d N : ℕ) (hN : 0<N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) : (∫ x, density d N p hp hs x)=1 := by
  rw [density, sampleInterpolate_integral d N (by exact_mod_cast hN)]
  · exact (YoungCompatibility.hasSum_probability _).tsum_eq
  · exact (YoungCompatibility.hasSum_probability _).summable

theorem density_nonneg (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (x : rootSpace d) : 0 ≤ density d N p hp hs x := by
  unfold density sampleInterpolate euclideanInterpolate interpolate
    YoungRounding.affineDensity YoungRounding.interpolate
  positivity

theorem integrable_density (d N : ℕ) (hN : 0<N) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) : Integrable (density d N p hp hs) := by
  by_contra h
  have he := integral_density d N hN p hp hs
  rw [integral_undef h] at he
  norm_num at he

end Cloning.CountMultinomial
