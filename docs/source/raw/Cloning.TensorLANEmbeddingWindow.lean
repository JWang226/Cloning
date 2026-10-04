import Cloning.TensorLANEmbeddingProtocolError

/-! Uniform physical LAN estimates on a bounded trace-zero parameter window,
for each sufficiently large fixed compression cutoff. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter MeasureTheory
namespace Cloning.TensorLAN
open Cloning.PCTPhysicalFidelity Cloning.TensorLie Cloning.PCTJointGaussianWhitening
open Cloning.PhysicalCloningConverse Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {k s : ℕ}
variable (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1))

theorem exists_cutoff_uniform_physical_protocol (B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ᶠ N in atTop, ∀ θ : Parameters k, ‖θ‖ ≤ B →
      (∑ a, θ.1 a = 0) →
      ‖(physicalCoordinateForward p b hb e N Q).map (chartTensor p θ N)-(model p b e θ).1‖ < ε ∧
      ‖(physicalCoordinateReverse p b hb e N Q).map (model p b e θ).1-chartTensor p θ N‖ < ε := by
  let K : Set (PositiveRoot (k+1) → ℂ) := Metric.closedBall 0 B
  have hK : IsCompact K := isCompact_closedBall 0 B
  obtain ⟨Q₀,hQ₀⟩ := exists_cutoff_uniform_physical_averages p.eigenvalue p.positive p.strictAnti
    p.normalized B K hK (ε/8) (by positivity)
  obtain ⟨N₁,hN₁⟩ := uniform_whitened_local_Young_l1 p.eigenvalue p.positive p.normalized
    p.strictAnti b hb B (ε/8) (by positivity)
  let H : Set (Fin (k+1) → ℝ) := {h | ‖h‖ ≤ B ∧ ∑ a, h a = 0}
  have hH : Bornology.IsBounded H := isBounded_iff_forall_norm_le.mpr ⟨B, fun h hh => hh.1⟩
  have hadm := eventually_localSpectrum_admissible p.eigenvalue p.positive p.strictAnti
    p.normalized H hH (fun h hh => hh.2)
  refine ⟨Q₀,?_⟩
  intro Q hQ
  filter_upwards [hQ₀ Q hQ, hadm, eventually_ge_atTop (max N₁ 1)] with N hN hA hsize θ hθ hzero
  have hh : ‖θ.1‖ ≤ B := (norm_fst_le θ).trans hθ
  have hz : θ.2 ∈ K := by
    change dist θ.2 0 ≤ B
    simpa only [dist_zero_right] using (norm_snd_le θ).trans hθ
  have ha := hA θ.1 ⟨hh,hzero⟩
  have havg := hN θ.1 hh hzero ha.1 ha.2.1.antitone θ.2 hz
  have hpos : 0 < N := by have ht := (le_max_right N₁ 1).trans hsize; omega
  have hclass : classicalLocalError p b hb N θ.1 < ε/8 := by
    have hc := hN₁ N ((le_max_left _ _).trans hsize) θ.1 hh hzero ha.1
    have he := physicalLabelDensity_eq_whitened p.eigenvalue p.positive b hb N hpos
      (localSpectrum p.eigenvalue θ.1 N) (fun a => (ha.1 a).le)
      (localSpectrum_sum p.eigenvalue θ.1 p.normalized hzero N)
    unfold classicalLocalError
    rw [he]
    exact hc
  have he := physicalCoordinate_errors_le p b hb e N Q hpos θ hzero ha.1
  constructor
  · linarith [he.1,havg.1]
  · linarith [he.2,havg.2]

end Cloning.TensorLAN
