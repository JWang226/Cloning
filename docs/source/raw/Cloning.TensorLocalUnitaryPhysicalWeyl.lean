import Cloning.TensorLocalUnitaryWeyl
import Cloning.TensorLocalUnitaryCoordinates

/-! The Weyl limit for the literal physical tensor power of the local orbital
chart rotation, with its exact physical sample-size normalization. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.L2Operator
open Filter NormedSpace
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN Cloning.MultimodeCoherent Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {d : ℕ}
variable (p : Fin d → ℝ) (hp : ∀ a : PositiveRoot d, 0 < p a.val.1-p a.val.2)
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (hfreq : Tendsto (fun N => fun a => (mu N a : ℝ)/((∑ b, mu N b : ℕ) : ℝ)) atTop (𝓝 p))
    (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀))
include hp hδ hgap hfreq hz

/-- Actual physical local rotations converge to actual Weyl displacements on
every retained occupation-frame vector, uniformly after a sufficiently large
fixed compression cutoff. All coefficient and scale adapters are discharged. -/
theorem exists_cutoff_eventually_physical_orbital_frame
    (R : ℕ) (i : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀, ∀ᶠ N in atTop,
      ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
          (tensorOperator (∑ j, mu N j)
            (exp (sampleScale (∑ j, mu N j) • orbitalGenerator p (z N)))
            (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)) -
        displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)‖ < ε := by
  let z' N := scaledRootParameter p (mu N) (sampleScale (∑ j, mu N j)) (z N)
  have hz' : Tendsto z' atTop (𝓝 z₀) :=
    scaledRootParameter_tendsto p hp mu hmu (fun N => ∑ j, mu N j) hfreq z z₀ hz
  obtain ⟨Q₀,hRQ,hQ₀⟩ := exists_cutoff_eventually_frame_displacement
    mu hmu δ hδ hgap z' z₀ hz' R i ε hε
  refine ⟨Q₀,hRQ,?_⟩
  intro Q hQ
  filter_upwards [hQ₀ Q hQ,hgap,hδ.eventually (eventually_gt_atTop 0)] with N hN hg hpos
  have hg' : ∀ a : PositiveRoot d, 0 < (mu N a.val.1 : ℝ)-mu N a.val.2 :=
    fun a => hpos.trans_le (hg a)
  simpa only [tensorOperator_local_orbital p (mu N) hg', z'] using hN

/-- The same concrete compression maps have the reverse local-rotation limit. -/
theorem exists_cutoff_eventually_physical_orbital_frame_reverse
    (R : ℕ) (i : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀, ∀ᶠ N in atTop,
      ‖(cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q).adjoint
          (displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)) -
        tensorOperator (∑ j, mu N j)
          (exp (sampleScale (∑ j, mu N j) • orbitalGenerator p (z N)))
          (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖ < ε := by
  let z' N := scaledRootParameter p (mu N) (sampleScale (∑ j, mu N j)) (z N)
  have hz' : Tendsto z' atTop (𝓝 z₀) :=
    scaledRootParameter_tendsto p hp mu hmu (fun N => ∑ j, mu N j) hfreq z z₀ hz
  obtain ⟨Q₀,hRQ,hQ₀⟩ := exists_cutoff_eventually_frame_displacement_reverse
    mu hmu δ hδ hgap z' z₀ hz' R i ε hε
  refine ⟨Q₀,hRQ,?_⟩
  intro Q hQ
  filter_upwards [hQ₀ Q hQ,hgap,hδ.eventually (eventually_gt_atTop 0)] with N hN hg hpos
  have hg' : ∀ a : PositiveRoot d, 0 < (mu N a.val.1 : ℝ)-mu N a.val.2 :=
    fun a => hpos.trans_le (hg a)
  simpa only [tensorOperator_local_orbital p (mu N) hg', z'] using hN

end Cloning.TensorLocalUnitary
