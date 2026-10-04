import Cloning.TensorLANEmbeddingWindow
import Cloning.TensorLANEmbeddingDiagonal

/-! One genuine all-input physical channel sequence realizes mixed LAN on
all compact trace-zero windows simultaneously. The cutoff is fixed before
any compact parameter set is supplied. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter
namespace Cloning.TensorLAN
open Cloning.PCTPhysicalFidelity Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ}

/-- Unconditional existence of the literal compact-window physical LAN maps
for every strictly ordered positive spectrum and every allowed coordinate
frame and mode enumeration. -/
theorem nonempty_physicalCompactWindowLAN (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1)) :
    Nonempty (CompactWindowLAN p b e) := by
  have hex (j : ℕ) := exists_cutoff_uniform_physical_protocol p b hb e (j : ℝ)
    (1/((j : ℝ)+1)) (by positivity)
  choose Q hQ using hex
  let cutoff (j : ℕ) := max j (Q j)
  let P (N j : ℕ) : Prop := ∀ θ : Parameters k, ‖θ‖ ≤ (j : ℝ) → (∑ a, θ.1 a = 0) →
    ‖(physicalCoordinateForward p b hb e N (cutoff j)).map (chartTensor p θ N)-(model p b e θ).1‖ < 1/((j : ℝ)+1) ∧
    ‖(physicalCoordinateReverse p b hb e N (cutoff j)).map (model p b e θ).1-chartTensor p θ N‖ < 1/((j : ℝ)+1)
  have hP (j : ℕ) : ∀ᶠ N in atTop, P N j := hQ j (cutoff j) (le_max_right _ _)
  obtain ⟨ell,hellMono,hell,hellBound,hvalid⟩ := exists_common_diverging_cutoff P hP
  refine ⟨{ forward := fun N => physicalCoordinateForward p b hb e N (cutoff (ell N))
            reverse := fun N => physicalCoordinateReverse p b hb e N (cutoff (ell N))
            approximation := ?_ }⟩
  intro K hK hzero
  obtain ⟨B,hB,hKB⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨j,hj⟩ := exists_nat_ge B
  refine ⟨fun N => 1/((ell N : ℝ)+1), ?_, ?_⟩
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hell
  · filter_upwards [hvalid, hell.eventually (eventually_ge_atTop j)] with N hN hjN θ hθ
    have hn : ‖θ‖ ≤ (ell N : ℝ) := (hKB θ hθ).trans (hj.trans (by exact_mod_cast hjN))
    exact ⟨(hN (ell N) le_rfl θ hn (hzero θ hθ)).1.le,
      (hN (ell N) le_rfl θ hn (hzero θ hθ)).2.le⟩

/-- A fixed chosen witness of the actual physical LAN channel sequence. -/
def physicalCompactWindowLAN (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin s ≃ PairIndex (k+1)) :
    CompactWindowLAN p b e :=
  Classical.choice (nonempty_physicalCompactWindowLAN p b hb e)

end Cloning.TensorLAN
