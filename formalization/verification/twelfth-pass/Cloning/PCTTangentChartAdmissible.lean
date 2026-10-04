import Cloning.PCTTangentChartFrame

/-! Admissibility and a fixed compact parameter window for the exact physical
PCT tangent chart. These are the hypotheses consumed by bounded-window LAN;
no LAN channel or LAN approximation statement is assumed here. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
open Matrix NormedSpace Filter
namespace Cloning.PCTLocalChart
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [LinearOrder A]

/-- The literal local eigenvalues in the exact chart. -/
def sampleEigenvalues (p : A → ℝ) (hp : Function.Injective p) (Z : Matrix A A ℂ)
    (L : ℕ) (i : A) : ℝ := p i + sampleScale L * spectralCoordinates (sampleTangent p hp Z L) i

lemma sampleEigenvalues_tendsto (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) (i : A) :
    Tendsto (fun L => sampleEigenvalues p hp Z L i) atTop (𝓝 (p i)) := by
  have h := (tendsto_pi_nhds.mp (sampleSpectralCoordinates_tendsto p hp Z)) i
  simpa only [zero_mul, add_zero, sampleEigenvalues] using
    tendsto_const_nhds.add (sampleScale_tendsto.mul h)

/-- Every eigenvalue stays strictly positive eventually at a full-rank base. -/
theorem eventually_sampleEigenvalues_positive (p : A → ℝ) (hp : Function.Injective p)
    (hp0 : ∀ i, 0 < p i) (Z : Matrix A A ℂ) :
    ∀ᶠ L : ℕ in atTop, ∀ i, 0 < sampleEigenvalues p hp Z L i := by
  apply eventually_all.mpr
  intro i
  exact (tendsto_order.mp (sampleEigenvalues_tendsto p hp Z i)).1 0 (hp0 i)

/-- Every strict spectral gap remains open for all sufficiently large samples. -/
theorem eventually_sampleEigenvalues_ordered (p : A → ℝ) (hp : Function.Injective p)
    (hgap : ∀ i j, i < j → p j < p i) (Z : Matrix A A ℂ) :
    ∀ᶠ L : ℕ in atTop, ∀ i j, i < j →
      sampleEigenvalues p hp Z L j < sampleEigenvalues p hp Z L i := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : i < j
  · have h := ((sampleEigenvalues_tendsto p hp Z i).sub (sampleEigenvalues_tendsto p hp Z j))
    filter_upwards [(tendsto_order.mp h).1 0 (sub_pos.mpr (hgap i j hij))] with L hL
    intro _
    exact sub_pos.mp hL
  · exact Filter.Eventually.of_forall (fun _ h => (hij h).elim)

/-- The scaled spectral and orbital parameters, in their fixed finite-dimensional
ambient space. The spectral trace-zero constraint is proved separately below. -/
def sampleParameters (p : A → ℝ) (hp : Function.Injective p) (Z : Matrix A A ℂ) (L : ℕ) :
    (A → ℝ) × (OrbitalPair A → ℂ) :=
  (spectralCoordinates (sampleTangent p hp Z L), orbitalCoordinates p (sampleTangent p hp Z L))

def tangentParameters (p : A → ℝ) (Z : Matrix A A ℂ) : (A → ℝ) × (OrbitalPair A → ℂ) :=
  (classicalCoordinate p Z, fun ij => orbitalCoordinate p Z ij.1.1 ij.1.2)

theorem sampleParameters_tendsto (p : A → ℝ) (hp : Function.Injective p) (Z : Matrix A A ℂ) :
    Tendsto (sampleParameters p hp Z) atTop (𝓝 (tangentParameters p Z)) := by
  simpa only [sampleParameters, tangentParameters, nhds_prod_eq] using
    (sampleSpectralCoordinates_tendsto p hp Z).prodMk (sampleOrbitalCoordinates_tendsto p hp Z)

/-- One fixed compact ball contains the entire tail of the exact scaled
parameter sequence. Its radius is determined by the fixed physical tangent. -/
theorem exists_compact_ball_sampleParameters (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (Metric.closedBall (0 : (A → ℝ) × (OrbitalPair A → ℂ)) R) ∧
      ∀ᶠ L : ℕ in atTop, sampleParameters p hp Z L ∈ Metric.closedBall 0 R := by
  let R := ‖tangentParameters p Z‖ + 1
  refine ⟨R, by dsimp [R]; positivity, isCompact_closedBall 0 R, ?_⟩
  have hn := (sampleParameters_tendsto p hp Z).norm
  have hR : ‖tangentParameters p Z‖ < R := by dsimp [R]; linarith
  filter_upwards [(tendsto_order.mp hn).2 R hR] with L hL
  simpa only [Metric.mem_closedBall, dist_zero_right] using hL.le

/-- A compact subset of the actual trace-zero parameter hyperplane contains
the tail whenever the tangent purification is normalized and orthogonal. -/
theorem exists_compact_traceZero_sampleParameters
    (p : A → ℝ) (hp : Function.Injective p) (hp0 : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0) :
    ∃ K : Set ((A → ℝ) × (OrbitalPair A → ℂ)), IsCompact K ∧
      (∀ θ ∈ K, ∑ i, θ.1 i = 0) ∧ ∀ᶠ L : ℕ in atTop, sampleParameters p hp Z L ∈ K := by
  obtain ⟨R, _, hR, htail⟩ := exists_compact_ball_sampleParameters p hp Z
  let H : Set ((A → ℝ) × (OrbitalPair A → ℂ)) := {θ | ∑ i, θ.1 i = 0}
  have hH : IsClosed H := by
    apply isClosed_eq _ continuous_const
    fun_prop
  refine ⟨Metric.closedBall 0 R ∩ H, hR.inter_right hH, fun θ hθ => hθ.2, ?_⟩
  filter_upwards [htail, eventually_sample_spectral_sum_zero p hp hp0 hs Z horth] with L hL hzero
  exact ⟨hL, hzero⟩

/-- Admissible ordered, normalized, full-rank local eigenvalues and one fixed
compact parameter window are obtained from the physical tangent assumptions. -/
theorem eventually_sample_chart_admissible
    (p : A → ℝ) (hp : Function.Injective p) (hp0 : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (hgap : ∀ i j, i < j → p j < p i)
    (Z : Matrix A A ℂ)
    (horth : ⟪coefficientVector (schmidtCoefficients p), coefficientVector Z⟫_ℂ = 0) :
    ∃ K : Set ((A → ℝ) × (OrbitalPair A → ℂ)), IsCompact K ∧
      (∀ θ ∈ K, ∑ i, θ.1 i = 0) ∧
      ∀ᶠ L : ℕ in atTop, sampleParameters p hp Z L ∈ K ∧
        (∀ i, 0 < sampleEigenvalues p hp Z L i) ∧
        (∀ i j, i < j → sampleEigenvalues p hp Z L j < sampleEigenvalues p hp Z L i) ∧
        ∑ i, sampleEigenvalues p hp Z L i = 1 := by
  obtain ⟨K, hK, hzero, htail⟩ := exists_compact_traceZero_sampleParameters p hp
    (fun i => (hp0 i).le) hs Z horth
  refine ⟨K, hK, hzero, ?_⟩
  filter_upwards [htail, eventually_sampleEigenvalues_positive p hp hp0 Z,
    eventually_sampleEigenvalues_ordered p hp hgap Z] with L hL hpos hord
  refine ⟨hL, hpos, hord, ?_⟩
  have hz := hzero _ hL
  change (∑ i, (p i + sampleScale L * spectralCoordinates (sampleTangent p hp Z L) i)) = 1
  rw [Finset.sum_add_distrib, hs, ← Finset.mul_sum]
  change 1 + sampleScale L * (∑ i, (sampleParameters p hp Z L).1 i) = 1
  rw [hz, mul_zero, add_zero]

end Cloning.PCTLocalChart
