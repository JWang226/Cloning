import Cloning.TensorLocalUnitaryFockPolynomial

/-! Uniformly small physical exponential tails combined with the proved
finite polynomial limit. This is the physical half of the Weyl limit. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter NormedSpace
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {d : ℕ}

def oscillatorTaylor (Q : ℕ) (z : PositiveRoot d → ℂ) (w : List (PositiveRoot d)) (m : ℕ) :
    RootFock d :=
  ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) •
    (∑ i, (((oscillatorCutoffMatrix Q z)^j).mulVec
      (limitingWordCoordinates Q w) i) • cutoffNumberFrame d Q i)

/-- Choose a Taylor order first, then any sufficiently large fixed cutoff.
The actual physical exponential approaches that oscillator polynomial to
arbitrary precision, for every convergent displacement sequence. -/
theorem exists_order_eventually_exponential_near_polynomial
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀))
    (w : List (PositiveRoot d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ Q : ℕ, loweringHeight w+m*d ≤ Q →
      ∀ᶠ N in atTop,
        ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
            (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
              (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)) -
          oscillatorTaylor Q z₀ w m‖ < ε := by
  let R := loweringHeight w
  let B := (∑ a, ‖z₀ a‖)+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hzsum : Tendsto (fun N => ∑ a, ‖z N a‖) atTop (𝓝 (∑ a, ‖z₀ a‖)) :=
    tendsto_finset_sum _ (fun a _ => (tendsto_pi_nhds.mp hz a).norm)
  have hzB : ∀ᶠ N in atTop, (∑ a, ‖z N a‖) ≤ B :=
    (hzsum.eventually_lt_const (by dsimp [B]; linarith)).mono (fun _ h => h.le)
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((uniformTaylorBound_tendsto B hB R d).eventually_lt_const (show 0 < ε/4 by linarith))
  refine ⟨M, ?_⟩
  intro m hm Q hQ
  have hsmall := hM m hm
  have hnorm : ∀ᶠ N in atTop,
      ‖normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w‖ ≤ 2 :=
    ((partition_normalizedWord_norm_tendsto mu hmu δ hδ hgap w).eventually_lt_const
      (by norm_num : (1 : ℝ)<2)).mono (fun _ h => h.le)
  have hpoly := cutoffEmbedding_taylor_tendsto mu hmu δ hδ hgap z z₀ hz R Q m hQ w le_rfl
  have hpolyerr := (tendsto_iff_norm_sub_tendsto_zero.mp hpoly).eventually_lt_const
    (show 0 < ε/2 by linarith)
  have hlarge := hδ.eventually (eventually_ge_atTop (2*(((R+(m+1)*d : ℕ) : ℝ)+1)))
  filter_upwards [hzB,hnorm,hpolyerr,hgap,hlarge,
    cutoffEmbedding_eventually_contraction mu hmu δ hδ hgap Q] with N hzN hnN hpN hgN hLN hV
  let x := normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w
  let G := rootGenerator (n := ∑ j, mu N j) (mu N) (z N)
  let T := ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) • ((G^j) x)
  have hx : x ∈ cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (R : ℤ) :=
    normalizedLoweringWord_mem_cyclicCutoff _ _ _ (by exact_mod_cast (le_rfl : loweringHeight w ≤ R))
  have hrem : ‖exp G x - T‖ < ε/2 := by
    have hr := exp_rootGenerator_taylor_remainder
      (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (z N) R m
      (fun a => hLN.trans (hgN a)) hx
    have hb : ‖exp G x - T‖ ≤ uniformTaylorBound B R d m * 2 := by
      apply hr.trans
      unfold uniformTaylorBound
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply mul_le_mul _ hnN (norm_nonneg _) (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hzN (by norm_num)) (Real.sqrt_nonneg _)
    linarith
  let V := cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
  have hV' : ∀ y, ‖V y‖ ≤ ‖y‖ := hV
  change ‖V T - oscillatorTaylor Q z₀ w m‖ < ε/2 at hpN
  have hVT : ‖V (exp G x) - V T‖ ≤ ‖exp G x - T‖ := by
    rw [← V.map_sub]
    exact hV' (exp G x - T)
  calc
    ‖V (exp G x) - oscillatorTaylor Q z₀ w m‖ ≤
        ‖V (exp G x) - V T‖ + ‖V T - oscillatorTaylor Q z₀ w m‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖exp G x - T‖ + ‖V T - oscillatorTaylor Q z₀ w m‖ := add_le_add hVT le_rfl
    _ < ε := by linarith

end Cloning.TensorLocalUnitary
