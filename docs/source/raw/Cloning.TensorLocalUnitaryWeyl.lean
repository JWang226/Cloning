import Cloning.TensorLocalUnitaryApproximation
import Cloning.TensorLocalUnitaryReverse
import Cloning.TensorWeylMatrixPowers

/-! The actual physical local unitary converges to the actual Weyl displacement
under the concrete cutoff transports, in both vector directions. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter NormedSpace
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {n d : ℕ}

theorem oscillatorTaylor_eq_numberTaylor (Q m : ℕ) (z : PositiveRoot d → ℂ)
    (w : List (PositiveRoot d)) (hQ : loweringHeight w+m*d ≤ Q) :
    oscillatorTaylor Q z w m = numberTaylor (rootFockAmplitude z) (wordFockOccupation w) m := by
  unfold oscillatorTaylor numberTaylor
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact oscillatorCutoffMatrix_power_eq_numberPower Q j z w
    ((Nat.add_le_add_left (Nat.mul_le_mul_right d (by have := Finset.mem_range.mp hj; omega))
      (loweringHeight w)).trans hQ)

theorem rootGenerator_exp_norm (mu : Fin d → ℕ) (z : PositiveRoot d → ℂ)
    (x : TensorRegister n (Fin d)) : ‖exp (rootGenerator (n := n) mu z) x‖ = ‖x‖ := by
  simpa only [expOrbit, one_smul] using expOrbit_norm _ (rootGenerator_skew mu z) x 1

variable (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀))
include hδ hgap hz

/-- Actual normalized PBW input, actual physical exponential, actual Fock
partial isometry, and actual Weyl output. The cutoff is fixed before taking
the partition limit and may be any sufficiently large value. -/
theorem exists_cutoff_eventually_word_displacement
    (w : List (PositiveRoot d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ᶠ N in atTop,
      ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
          (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
            (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)) -
        displacement (rootFockAmplitude z₀) (wordNumberVector w)‖ < ε := by
  obtain ⟨M,hM⟩ := exists_order_eventually_exponential_near_polynomial
    mu hmu δ hδ hgap z z₀ hz w (ε/2) (by linarith)
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mp
    (numberTaylor_tendsto_displacement (rootFockAmplitude z₀) (wordFockOccupation w))).eventually_lt_const
      (show 0 < ε/2 by linarith)
  obtain ⟨m,hm,hmt⟩ := ((eventually_ge_atTop M).and ht).exists
  refine ⟨loweringHeight w+m*d, ?_⟩
  intro Q hQ
  filter_upwards [hM m hm Q hQ] with N hN
  rw [oscillatorTaylor_eq_numberTaylor Q m z₀ w hQ] at hN
  have hh := norm_sub_le_norm_sub_add_norm_sub
    (cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
      (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
        (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)))
    (numberTaylor (rootFockAmplitude z₀) (wordFockOccupation w) m)
    (displacement (rootFockAmplitude z₀) (wordNumberVector w))
  change ‖numberTaylor (rootFockAmplitude z₀) (wordFockOccupation w) m -
    displacement (rootFockAmplitude z₀) (wordNumberVector w)‖ < ε/2 at hmt
  linarith

/-- The actual complete common-frame vectors needed for the Gibbs mixtures
have the same physical Weyl limit as their normalized PBW representatives. -/
theorem exists_cutoff_eventually_frame_displacement
    (R : ℕ) (i : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀, ∀ᶠ N in atTop,
      ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
          (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
            (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)) -
        displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)‖ < ε := by
  obtain ⟨Q₀,hQ₀⟩ := exists_cutoff_eventually_word_displacement
    mu hmu δ hδ hgap z z₀ hz (cutoffWord d R i) (ε/2) (by linarith)
  refine ⟨max R Q₀,le_max_left _ _,?_⟩
  intro Q hQ
  have hc := (partition_cutoffFrame_close mu hmu δ hδ hgap R i).eventually_lt_const
    (show 0 < ε/2 by linarith)
  filter_upwards [hQ₀ Q ((le_max_right _ _).trans hQ),hc,
    cutoffEmbedding_eventually_contraction mu hmu δ hδ hgap Q] with N hN hcN hV
  let V := cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
  let G := rootGenerator (n := ∑ j, mu N j) (mu N) (z N)
  let x := cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i
  let y := cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i
  have hclose : ‖V (exp G x)-V (exp G y)‖ < ε/2 := by
    rw [← V.map_sub, ← (exp G).map_sub]
    exact ((hV _).trans_eq (rootGenerator_exp_norm (mu N) (z N) (x-y))).trans_lt hcN
  rw [← cutoffNumberFrame_eq_word] at hN
  have hh := norm_sub_le_norm_sub_add_norm_sub (V (exp G x)) (V (exp G y))
    (displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i))
  change ‖V (exp G y)-displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)‖ < ε/2 at hN
  linarith

/-- Reverse approximation uses the actual adjoint of the same cutoff map. -/
theorem exists_cutoff_eventually_frame_displacement_reverse
    (R : ℕ) (i : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀, ∀ᶠ N in atTop,
      ‖(cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q).adjoint
          (displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)) -
        exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
          (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖ < ε := by
  obtain ⟨Q₀,hRQ,hQ₀⟩ := exists_cutoff_eventually_frame_displacement
    mu hmu δ hδ hgap z z₀ hz R i (ε^2/4) (by positivity)
  refine ⟨Q₀,hRQ,?_⟩
  intro Q hQ
  filter_upwards [hQ₀ Q hQ,cutoffEmbedding_eventually_contraction mu hmu δ hδ hgap Q,
    partition_eventually_cutoffOrthonormalBasis mu hmu δ hδ hgap R] with N hN hV hb
  obtain ⟨b,hb⟩ := hb
  have hx : ‖exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
      (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖ = 1 := by
    rw [rootGenerator_exp_norm, ← hb i]
    exact b.orthonormal.norm_eq_one i
  have hy : ‖displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)‖ = 1 := by
    rw [displacement_norm]
    exact (cutoffNumberFrame_orthonormal d R).norm_eq_one i
  have hrev := reverse_unit_vector_norm_sq_le _ hV _ _ hx hy
  nlinarith [norm_nonneg ((cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q).adjoint
    (displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)) -
      exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
        (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i))]

end Cloning.TensorLocalUnitary
