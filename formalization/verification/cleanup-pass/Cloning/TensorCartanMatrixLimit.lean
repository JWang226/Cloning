import Cloning.TensorCartanSplitCoefficients
import Cloning.TensorCyclicGramLimit

/-! Fixed-word matrix elements of the literal physical Cartan inclusion converge
to the finite occupation-splitting formula. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def partitionNormalizedLoweringWord (mu : Fin d → ℕ) (hmu : Antitone mu)
    (w : List (PositiveRoot d)) :=
  normalizedLoweringWord (partitionHighestTensor mu hmu) mu w

def cartanWordMatrixElement (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (w u v : List (PositiveRoot d)) : ℂ :=
  ⟪tensorJoin (partitionNormalizedLoweringWord mu hmu u)
      (partitionNormalizedLoweringWord nu hnu v),
    cartanAmbientInclusion mu nu hmu hnu
      (normalizedSectorWord (partitionHighestTensor (fun a => mu a + nu a)
        (sumPartition_antitone mu nu hmu hnu)) (fun a => mu a + nu a) w)⟫_ℂ

def occupationSplitMatrixElement (t : PositiveRoot d → ℝ)
    (w u v : List (PositiveRoot d)) : ℂ :=
  ((loweringSplits w).map (fun ab =>
    (splitFactorialCoefficient w ab.1 ab.2 * (wordAmplitude t ab.1 : ℂ) *
      (wordAmplitude (fun a => 1 - t a) ab.2 : ℂ)) *
      ((if u.Perm ab.1 then 1 else 0 : ℂ) * (if v.Perm ab.2 then 1 else 0 : ℂ)))).sum

/-- Exact physical matrix elements are finite sums of explicit splitting
coefficients times the actual Gram entries in the two factor sectors. -/
theorem cartanWordMatrixElement_eq_sum
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuGap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnuGap : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w u v : List (PositiveRoot d)) :
    cartanWordMatrixElement mu nu hmu hnu w u v =
      ((loweringSplits w).map (fun ab => normalizedSplitCoefficient mu nu w ab.1 ab.2 *
        (⟪partitionNormalizedLoweringWord mu hmu u,
          partitionNormalizedLoweringWord mu hmu ab.1⟫_ℂ *
         ⟪partitionNormalizedLoweringWord nu hnu v,
          partitionNormalizedLoweringWord nu hnu ab.2⟫_ℂ))).sum := by
  unfold cartanWordMatrixElement
  rw [cartanAmbientInclusion_word_split mu nu hmu hnu hmuGap hnuGap]
  change innerSL ℂ (tensorJoin (partitionNormalizedLoweringWord mu hmu u)
    (partitionNormalizedLoweringWord nu hnu v)) _ = _
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def, innerSL_apply_apply, inner_smul_right,
    tensorJoin_inner, partitionNormalizedLoweringWord]

/-- The actual Cartan matrix-element limit, with every physical Gram and
intertwining premise discharged by the tensor constructions. Both sector root
gaps diverge and their fractions converge; the three words remain fixed. -/
theorem cartanWordMatrixElement_tendsto
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (w u v : List (PositiveRoot d)) :
    Tendsto (fun N => cartanWordMatrixElement (mu N) (nu N) (hmu N) (hnu N) w u v)
      atTop (𝓝 (occupationSplitMatrixElement t w u v)) := by
  have hμpos : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, 0 < rootGap (mu N) a := by
    filter_upwards [hmuGap, hδmu.eventually (eventually_gt_atTop 0)] with N hN hp
    exact fun a => hp.trans_le (hN a)
  have hνpos : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, 0 < rootGap (nu N) a := by
    filter_upwards [hnuGap, hδnu.eventually (eventually_gt_atTop 0)] with N hN hp
    exact fun a => hp.trans_le (hN a)
  have hsum : Tendsto (fun N =>
      ((loweringSplits w).map (fun ab => normalizedSplitCoefficient (mu N) (nu N) w ab.1 ab.2 *
        (⟪partitionNormalizedLoweringWord (mu N) (hmu N) u,
          partitionNormalizedLoweringWord (mu N) (hmu N) ab.1⟫_ℂ *
         ⟪partitionNormalizedLoweringWord (nu N) (hnu N) v,
          partitionNormalizedLoweringWord (nu N) (hnu N) ab.2⟫_ℂ))).sum)
      atTop (𝓝 (occupationSplitMatrixElement t w u v)) := by
    apply tendsto_list_sum
    intro ab hab
    have hA := partition_normalized_gram_tendsto (fun a : PositiveRoot d => a)
      Function.injective_id mu hmu δmu hδmu hmuGap u ab.1
    have hB := partition_normalized_gram_tendsto (fun a : PositiveRoot d => a)
      Function.injective_id nu hnu δnu hδnu hnuGap v ab.2
    exact (normalizedSplitCoefficient_tendsto_complement mu nu hμpos hνpos t ht w ab.1 ab.2 hab).mul
      (hA.mul hB)
  apply hsum.congr'
  filter_upwards [hμpos, hνpos] with N hμ hν
  exact (cartanWordMatrixElement_eq_sum (mu N) (nu N) (hmu N) (hnu N) hμ hν w u v).symm

end Cloning.TensorLie
