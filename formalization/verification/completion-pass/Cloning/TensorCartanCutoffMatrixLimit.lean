import Cloning.TensorCartanCutoffFrame

/-! Transport of actual Cartan matrix-element convergence to the complete,
common orthonormal cutoff frames. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem varying_inner_tendsto_of_two_close
    {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, InnerProductSpace ℂ (H N)]
    (x y z w : ∀ N, H N) (a b : ℝ) (c : ℂ)
    (hxy : Tendsto (fun N => ‖x N - y N‖) atTop (𝓝 0))
    (hzw : Tendsto (fun N => ‖z N - w N‖) atTop (𝓝 0))
    (hy : Tendsto (fun N => ‖y N‖) atTop (𝓝 a))
    (hz : Tendsto (fun N => ‖z N‖) atTop (𝓝 b))
    (hyw : Tendsto (fun N => ⟪y N, w N⟫_ℂ) atTop (𝓝 c)) :
    Tendsto (fun N => ⟪x N, z N⟫_ℂ) atTop (𝓝 c) := by
  have he (N) : ⟪x N, z N⟫_ℂ - ⟪y N, w N⟫_ℂ =
      ⟪x N - y N, z N⟫_ℂ + ⟪y N, z N - w N⟫_ℂ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hlim := (hxy.mul hz).add (hy.mul hzw)
  simp only [zero_mul, mul_zero, add_zero] at hlim
  have hnorm : Tendsto (fun N => ‖⟪x N,z N⟫_ℂ - ⟪y N,w N⟫_ℂ‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro N
    rw [he N]
    exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
  have h := ((tendsto_zero_iff_norm_tendsto_zero).mpr hnorm).add hyw
  simpa only [sub_add_cancel, zero_add] using h

theorem tensorJoin_sub_le {n m : ℕ} (x u : TensorRegister n (Fin d))
    (y v : TensorRegister m (Fin d)) :
    ‖tensorJoin x y - tensorJoin u v‖ ≤ ‖x - u‖ * ‖y‖ + ‖u‖ * ‖y - v‖ := by
  have he : tensorJoin x y - tensorJoin u v = tensorJoin (x - u) y + tensorJoin u (y - v) := by
    ext z
    simp only [tensorJoin_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_add, Pi.add_apply]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [tensorJoin_norm, tensorJoin_norm])

theorem partition_cutoffRawFrame_norm_tendsto
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (R : ℕ) (i : CutoffIndex d R) :
    Tendsto (fun N => ‖cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i‖)
      atTop (𝓝 1) := by
  apply varying_vector_norm_tendsto
  intro i j
  simpa only [cutoffRawFrame, normalizedLoweringWord, cutoffWord_perm_iff] using
    partition_normalized_gram_tendsto (fun a : PositiveRoot d => a) Function.injective_id
      mu hmu δ hδ hgap (cutoffWord d R i) (cutoffWord d R j)

theorem partition_cutoffFrame_norm_tendsto
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (R : ℕ) (i : CutoffIndex d R) :
    Tendsto (fun N => ‖cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i‖)
      atTop (𝓝 1) :=
  varying_norm_tendsto_of_close _ _ 1
    (partition_cutoffRawFrame_norm_tendsto mu hmu δ hδ hgap R i)
    (partition_cutoffFrame_close mu hmu δ hδ hgap R i)

def cartanCutoffFrameMatrixElement (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (R : ℕ) (i j k : CutoffIndex d R) : ℂ :=
  ⟪tensorJoin (cutoffFrame (partitionHighestTensor mu hmu) mu R j)
      (cutoffFrame (partitionHighestTensor nu hnu) nu R k),
    cartanAmbientInclusion mu nu hmu hnu
      (cutoffSectorFrame (partitionHighestTensor (fun a => mu a + nu a)
        (sumPartition_antitone mu nu hmu hnu)) (fun a => mu a + nu a) R i)⟫_ℂ

/-- The same concrete occupation-splitting limit holds in actual complete
orthonormal cutoff frames, after transporting all three physical PBW families. -/
theorem cartanCutoffFrameMatrixElement_tendsto
    (mu nu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N)) (hnu : ∀ N, Antitone (nu N))
    (δmu δnu : ℕ → ℝ) (hδmu : Tendsto δmu atTop atTop) (hδnu : Tendsto δnu atTop atTop)
    (hmuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (mu N) a)
    (hnuGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δnu N ≤ rootGap (nu N) a)
    (t : PositiveRoot d → ℝ)
    (ht : ∀ a, Tendsto (fun N => rootFraction (mu N) (nu N) a) atTop (𝓝 (t a)))
    (R : ℕ) (i j k : CutoffIndex d R) :
    Tendsto (fun N => cartanCutoffFrameMatrixElement (mu N) (nu N) (hmu N) (hnu N) R i j k)
      atTop (𝓝 (occupationSplitMatrixElement t (cutoffWord d R i)
        (cutoffWord d R j) (cutoffWord d R k))) := by
  let sumMu := fun N a => mu N a + nu N a
  have hsum : ∀ N, Antitone (sumMu N) := fun N => sumPartition_antitone _ _ (hmu N) (hnu N)
  have hsumGap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δmu N ≤ rootGap (sumMu N) a := by
    filter_upwards [hmuGap, hnuGap, hδnu.eventually (eventually_gt_atTop 0)] with N hμ hν hδ
    intro a
    rw [rootGap_add]
    linarith [hμ a, hν a]
  have hμclose := partition_cutoffFrame_close mu hmu δmu hδmu hmuGap R j
  have hνclose := partition_cutoffFrame_close nu hnu δnu hδnu hnuGap R k
  have hSclose := partition_cutoffFrame_close sumMu hsum δmu hδmu hsumGap R i
  have hμnorm := partition_cutoffRawFrame_norm_tendsto mu hmu δmu hδmu hmuGap R j
  have hνnorm := partition_cutoffRawFrame_norm_tendsto nu hnu δnu hδnu hnuGap R k
  have hνfnorm := partition_cutoffFrame_norm_tendsto nu hnu δnu hδnu hnuGap R k
  have hSfnorm := partition_cutoffFrame_norm_tendsto sumMu hsum δmu hδmu hsumGap R i
  apply varying_inner_tendsto_of_two_close
    (fun N => tensorJoin (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)
      (cutoffFrame (partitionHighestTensor (nu N) (hnu N)) (nu N) R k))
    (fun N => tensorJoin (cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)
      (cutoffRawFrame (partitionHighestTensor (nu N) (hnu N)) (nu N) R k))
    (fun N => cartanAmbientInclusion (mu N) (nu N) (hmu N) (hnu N)
      (cutoffSectorFrame (partitionHighestTensor (sumMu N) (hsum N)) (sumMu N) R i))
    (fun N => cartanAmbientInclusion (mu N) (nu N) (hmu N) (hnu N)
      (normalizedSectorWord (partitionHighestTensor (sumMu N) (hsum N)) (sumMu N) (cutoffWord d R i)))
    1 1 _
  · have h := (hμclose.mul hνfnorm).add (hμnorm.mul hνclose)
    simp only [zero_mul, mul_zero, add_zero] at h
    exact squeeze_zero (fun _ => norm_nonneg _) (fun N => tensorJoin_sub_le _ _ _ _) h
  · convert hSclose using 1
    ext N
    rw [← map_sub, LinearIsometry.norm_map]
    rfl
  · simpa only [tensorJoin_norm, one_mul] using hμnorm.mul hνnorm
  · simpa only [LinearIsometry.norm_map, Submodule.norm_coe] using hSfnorm
  · exact cartanWordMatrixElement_tendsto mu nu hmu hnu δmu δnu hδmu hδnu
      hmuGap hnuGap t ht (cutoffWord d R i) (cutoffWord d R j) (cutoffWord d R k)

end Cloning.TensorLie
