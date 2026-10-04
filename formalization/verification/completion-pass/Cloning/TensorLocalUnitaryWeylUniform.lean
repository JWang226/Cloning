import Cloning.TensorLocalUnitaryPhysicalWeyl

/-! Cutoff choices uniform over bounded limiting displacements. The Taylor
order is chosen before the physical partition and displacement sequences. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.L2Operator
open Filter NormedSpace
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.PCTLocalChart
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {d : ℕ}

theorem exists_uniform_order_eventually_exponential_near_polynomial
    (B : ℝ) (hB : 0 ≤ B) (w : List (PositiveRoot d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ Q : ℕ, loweringHeight w+m*d ≤ Q →
      ∀ (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
        (δ : ℕ → ℝ), Tendsto δ atTop atTop →
        (∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) →
      ∀ (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ),
        Tendsto z atTop (𝓝 z₀) → (∑ a, ‖z₀ a‖) ≤ B →
      ∀ᶠ N in atTop,
        ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
            (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
              (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)) -
          oscillatorTaylor Q z₀ w m‖ < ε := by
  let R := loweringHeight w
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((uniformTaylorBound_tendsto (B+1) (by linarith) R d).eventually_lt_const
      (show 0 < ε/4 by linarith))
  refine ⟨M, ?_⟩
  intro m hm Q hQ mu hmu δ hδ hgap z z₀ hz hz₀
  have hsmall := hM m hm
  have hzsum : Tendsto (fun N => ∑ a, ‖z N a‖) atTop (𝓝 (∑ a, ‖z₀ a‖)) :=
    tendsto_finset_sum _ (fun a _ => (tendsto_pi_nhds.mp hz a).norm)
  have hzB : ∀ᶠ N in atTop, (∑ a, ‖z N a‖) ≤ B+1 :=
    (hzsum.eventually_lt_const (by linarith)).mono (fun _ h => h.le)
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
    have hb : ‖exp G x - T‖ ≤ uniformTaylorBound (B+1) R d m * 2 := by
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


/-- The cutoff depends only on a limiting-amplitude bound, the retained word,
and the tolerance, before any choice of the physical sequences. -/
theorem exists_uniform_cutoff_eventually_word_displacement
    (B : ℝ) (hB : 0 ≤ B) (w : List (PositiveRoot d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
      ∀ (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
        (δ : ℕ → ℝ), Tendsto δ atTop atTop →
        (∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) →
      ∀ (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ),
        Tendsto z atTop (𝓝 z₀) → (∑ a, ‖z₀ a‖) ≤ B →
      ∀ᶠ N in atTop,
        ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
            (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
              (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)) -
          displacement (rootFockAmplitude z₀) (wordNumberVector w)‖ < ε := by
  obtain ⟨M,hM⟩ := exists_uniform_order_eventually_exponential_near_polynomial
    B hB w (ε/2) (by linarith)
  obtain ⟨K,hK⟩ := exists_uniform_weyl_taylor_order
    B hB (∑ j, wordFockOccupation w j) (ε/2) (by linarith)
  let m := max M K
  refine ⟨loweringHeight w+m*d, ?_⟩
  intro Q hQ mu hmu δ hδ hgap z z₀ hz hz₀
  have hsum : (∑ j, ‖rootFockAmplitude z₀ j‖) ≤ B := by
    rw [← Equiv.sum_comp (Fintype.equivFin (PositiveRoot d))]
    simpa only [rootFockAmplitude, Equiv.symm_apply_apply] using hz₀
  have ht := hK m (le_max_right _ _) (rootFockAmplitude z₀) hsum
    (wordFockOccupation w) (fun j => Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [norm_sub_rev] at ht
  filter_upwards [hM m (le_max_left _ _) Q hQ mu hmu δ hδ hgap z z₀ hz hz₀] with N hN
  rw [oscillatorTaylor_eq_numberTaylor Q m z₀ w hQ] at hN
  have hh := norm_sub_le_norm_sub_add_norm_sub
    (cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
      (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
        (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)))
    (numberTaylor (rootFockAmplitude z₀) (wordFockOccupation w) m)
    (displacement (rootFockAmplitude z₀) (wordNumberVector w))
  change ‖numberTaylor (rootFockAmplitude z₀) (wordFockOccupation w) m -
    displacement (rootFockAmplitude z₀) (wordNumberVector w)‖ < ε/2 at ht
  linarith

theorem exists_uniform_cutoff_eventually_frame_displacement
    (B : ℝ) (hB : 0 ≤ B) (R : ℕ) (i : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀,
      ∀ (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
        (δ : ℕ → ℝ), Tendsto δ atTop atTop →
        (∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) →
      ∀ (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ),
        Tendsto z atTop (𝓝 z₀) → (∑ a, ‖z₀ a‖) ≤ B →
      ∀ᶠ N in atTop,
        ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
            (exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
              (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)) -
          displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)‖ < ε := by
  obtain ⟨Q₀,hQ₀⟩ := exists_uniform_cutoff_eventually_word_displacement
    B hB (cutoffWord d R i) (ε/2) (by linarith)
  refine ⟨max R Q₀,le_max_left _ _,?_⟩
  intro Q hQ mu hmu δ hδ hgap z z₀ hz hz₀
  have hc := (partition_cutoffFrame_close mu hmu δ hδ hgap R i).eventually_lt_const
    (show 0 < ε/2 by linarith)
  filter_upwards [hQ₀ Q ((le_max_right _ _).trans hQ) mu hmu δ hδ hgap z z₀ hz hz₀,hc,
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

theorem exists_uniform_cutoff_eventually_frame_displacement_reverse
    (B : ℝ) (hB : 0 ≤ B) (R : ℕ) (i : CutoffIndex d R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀,
      ∀ (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
        (δ : ℕ → ℝ), Tendsto δ atTop atTop →
        (∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) →
      ∀ (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ),
        Tendsto z atTop (𝓝 z₀) → (∑ a, ‖z₀ a‖) ≤ B →
      ∀ᶠ N in atTop,
        ‖(cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q).adjoint
            (displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)) -
          exp (rootGenerator (n := ∑ j, mu N j) (mu N) (z N))
            (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖ < ε := by
  obtain ⟨Q₀,hRQ,hQ₀⟩ := exists_uniform_cutoff_eventually_frame_displacement
    B hB R i (ε^2/4) (by positivity)
  refine ⟨Q₀,hRQ,?_⟩
  intro Q hQ mu hmu δ hδ hgap z z₀ hz hz₀
  filter_upwards [hQ₀ Q hQ mu hmu δ hδ hgap z z₀ hz hz₀,
    cutoffEmbedding_eventually_contraction mu hmu δ hδ hgap Q,
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


/-- One cutoff handles every retained frame vector and both directions. It is
chosen from the amplitude bound, retained height and tolerance alone. -/
theorem exists_uniform_cutoff_eventually_physical_orbital_frames
    (B : ℝ) (hB : 0 ≤ B) (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, R ≤ Q₀ ∧ ∀ Q ≥ Q₀,
      ∀ (p : Fin d → ℝ), (∀ a : PositiveRoot d, 0 < p a.val.1-p a.val.2) →
      ∀ (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
        (δ : ℕ → ℝ), Tendsto δ atTop atTop →
        (∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) →
        Tendsto (fun N => fun a => (mu N a : ℝ)/((∑ b, mu N b : ℕ) : ℝ)) atTop (𝓝 p) →
      ∀ (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ),
        Tendsto z atTop (𝓝 z₀) → (∑ a, ‖z₀ a‖) ≤ B →
      ∀ᶠ N in atTop, ∀ i : CutoffIndex d R,
        (‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
            (tensorOperator (∑ j, mu N j)
              (exp (sampleScale (∑ j, mu N j) • orbitalGenerator p (z N)))
              (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)) -
          displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)‖ < ε) ∧
        (‖(cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q).adjoint
            (displacement (rootFockAmplitude z₀) (cutoffNumberFrame d R i)) -
          tensorOperator (∑ j, mu N j)
            (exp (sampleScale (∑ j, mu N j) • orbitalGenerator p (z N)))
            (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖ < ε) := by
  classical
  choose Qf hRf hf using fun i : CutoffIndex d R =>
    exists_uniform_cutoff_eventually_frame_displacement B hB R i ε hε
  choose Qr hRr hr using fun i : CutoffIndex d R =>
    exists_uniform_cutoff_eventually_frame_displacement_reverse B hB R i ε hε
  let Q₀ := max R (Finset.univ.sup fun i : CutoffIndex d R => max (Qf i) (Qr i))
  refine ⟨Q₀,le_max_left _ _,?_⟩
  intro Q hQ p hp mu hmu δ hδ hgap hfreq z z₀ hz hz₀
  let z' N := scaledRootParameter p (mu N) (sampleScale (∑ j, mu N j)) (z N)
  have hz' : Tendsto z' atTop (𝓝 z₀) :=
    scaledRootParameter_tendsto p hp mu hmu (fun N => ∑ j, mu N j) hfreq z z₀ hz
  have hQi (i : CutoffIndex d R) : max (Qf i) (Qr i) ≤ Q :=
    (Finset.le_sup (f := fun i : CutoffIndex d R => max (Qf i) (Qr i))
      (Finset.mem_univ i)).trans ((le_max_right _ _).trans hQ)
  have hfall := Filter.eventually_all.mpr (fun i =>
    hf i Q ((le_max_left _ _).trans (hQi i)) mu hmu δ hδ hgap z' z₀ hz' hz₀)
  have hrall := Filter.eventually_all.mpr (fun i =>
    hr i Q ((le_max_right _ _).trans (hQi i)) mu hmu δ hδ hgap z' z₀ hz' hz₀)
  filter_upwards [hfall,hrall,hgap,hδ.eventually (eventually_gt_atTop 0)] with N hNf hNr hg hpos
  intro i
  have hg' : ∀ a : PositiveRoot d, 0 < (mu N a.val.1 : ℝ)-mu N a.val.2 :=
    fun a => hpos.trans_le (hg a)
  constructor
  · simpa only [tensorOperator_local_orbital p (mu N) hg', z'] using hNf i
  · simpa only [tensorOperator_local_orbital p (mu N) hg', z'] using hNr i

end Cloning.TensorLocalUnitary
