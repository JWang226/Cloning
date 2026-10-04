import Cloning.TensorSchurDecompositionMultiplicity
import Cloning.YoungHyperplaneSampling

/-! The actual physical Young probability law on the complete affine integer
lattice, preserving the dependent last coordinate exactly. -/

noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
open Cloning.TensorLie Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Complete the head coordinates of any finite shape into the full affine
lattice; the physical law gives zero mass to inconsistent finite shapes. -/
def shapeLattice (d N : ℕ) (μ : Shape (d + 1) N) : Lattice d (N : ℤ) :=
  latticeCoordinates d N (fun i ↦ (μ i.castSucc).val)

theorem shapeLattice_apply (d N : ℕ) (μ : Shape (d + 1) N)
    (hμ : ∑ i, (μ i).val = N) (i : Fin (d + 1)) :
    (shapeLattice d N μ).1 i = ((μ i).val : ℤ) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have ht := (shapeLattice d N μ).2
    change (∑ i, (shapeLattice d N μ).1 i) = (N : ℤ) at ht
    rw [Fin.sum_univ_castSucc] at ht hμ
    have heq : ∀ j : Fin d, (shapeLattice d N μ).1 j.castSucc = ((μ j.castSucc).val : ℤ) :=
      fun j ↦ latticeCoordinates_head d N _ j
    simp only [heq] at ht
    have hcast : (∑ j : Fin d, ((μ j.castSucc).val : ℤ)) + ((μ (Fin.last d)).val : ℤ) = N := by
      exact_mod_cast hμ
    omega
  · exact latticeCoordinates_head d N _ j

theorem shapeLattice_injective_of_sum (d N : ℕ) (μ ν : Shape (d + 1) N)
    (hμ : ∑ i, (μ i).val = N) (hν : ∑ i, (ν i).val = N)
    (he : shapeLattice d N μ = shapeLattice d N ν) : μ = ν := by
  funext i
  apply Fin.ext
  have h := congrArg (fun z : Lattice d (N : ℤ) ↦ z.1 i) he
  dsimp only at h
  rw [shapeLattice_apply d N μ hμ, shapeLattice_apply d N ν hν] at h
  exact_mod_cast h

/-- The normalized, genuinely physical law on every affine lattice label. -/
def tensorYoungLatticePMF (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (Lattice d (N : ℤ)) :=
  (tensorYoungPMF N (d + 1) p hp hs).map (shapeLattice d N)

theorem tensorYoungLatticePMF_apply_shape (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (μ : Shape (d + 1) N)
    (hμ : ∑ i, (μ i).val = N) :
    tensorYoungLatticePMF d N p hp hs (shapeLattice d N μ) =
      tensorYoungPMF N (d + 1) p hp hs μ := by
  rw [tensorYoungLatticePMF, PMF.map_apply, tsum_eq_single μ]
  · simp
  · intro ν hν
    by_cases ht : ∑ i, (ν i).val = N
    · have hn : shapeLattice d N μ ≠ shapeLattice d N ν := by
        intro he
        exact hν (shapeLattice_injective_of_sum d N ν μ ht hμ he.symm)
      simp [hn]
    · have hz : tensorYoungPMF N (d + 1) p hp hs ν = 0 :=
        physicalYoungPMF_eq_zero_of_not_partition _ _ _ _ _ _ ν (Or.inr ht)
      simp [hz]

/-- Actual physical law interpolated on the manuscript's rescaled cells. -/
def tensorYoungDensity (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : rootSpace d → ℝ :=
  sampleInterpolate d N p (fun μ ↦ (tensorYoungLatticePMF d N p hp hs μ).toReal)

theorem tensorYoungDensity_eq_on_cell (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (μ : Shape (d + 1) N) (hμ : ∑ i, (μ i).val = N)
    (x : rootSpace d) (hx : x ∈ sampleCell d N p (shapeLattice d N μ)) :
    tensorYoungDensity d N p hp hs x =
      (Real.sqrt (N : ℝ) ^ d / Real.sqrt ((d : ℝ) + 1)) *
        (tensorYoungPMF N (d + 1) p hp hs μ).toReal := by
  unfold tensorYoungDensity
  rw [sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) p _ _ x hx,
    tensorYoungLatticePMF_apply_shape d N p hp hs μ hμ]
  norm_cast

/-- Exact normalization after smoothing the actual physical law. -/
theorem integral_tensorYoungDensity (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∫ x, tensorYoungDensity d N p hp hs x ∂volume) = 1 := by
  rw [tensorYoungDensity, sampleInterpolate_integral d N (by exact_mod_cast hN)]
  · exact (YoungCompatibility.hasSum_probability (tensorYoungLatticePMF d N p hp hs)).tsum_eq
  · exact (YoungCompatibility.hasSum_probability (tensorYoungLatticePMF d N p hp hs)).summable


theorem tensorYoungDensity_nonneg (d N : ℕ) (p : Fin (d + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (x : rootSpace d) :
    0 ≤ tensorYoungDensity d N p hp hs x := by
  unfold tensorYoungDensity sampleInterpolate euclideanInterpolate interpolate
    YoungRounding.affineDensity YoungRounding.interpolate
  positivity

theorem integrable_tensorYoungDensity (d N : ℕ) (hN : 0 < N)
    (p : Fin (d + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Integrable (tensorYoungDensity d N p hp hs) volume := by
  by_contra h
  have heq := integral_tensorYoungDensity d N hN p hp hs
  rw [integral_undef h] at heq
  norm_num at heq

end Cloning.YoungHyperplane
