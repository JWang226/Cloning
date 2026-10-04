import Cloning.TensorLocalUnitaryMatrixElements

/-! Root-generator convergence in the actual common orthonormal cutoff frame. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d : ℕ}
variable (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
include hδ hgap

/-- Even after applying a normalized creator, the actual GS frame remains
close to its physical normalized PBW word. -/
theorem partition_creator_frame_close (a : PositiveRoot d) (R : ℕ) (i : CutoffIndex d R) :
    Tendsto (fun N => ‖normalizedCreator (∑ j, mu N j) (mu N) a.val.1 a.val.2
        (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i) -
      normalizedCreator (∑ j, mu N j) (mu N) a.val.1 a.val.2
        (cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖)
      atTop (𝓝 0) := by
  have h := (partition_cutoffFrame_close mu hmu δ hδ hgap R i).const_mul
    (Real.sqrt (((R : ℝ)+1)*2))
  simp only [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ h
  filter_upwards [hgap, hδ.eventually (eventually_ge_atTop (2*((R : ℝ)+1)))] with N hg hL
  rw [← map_sub]
  exact normalizedCreator_cutoff_bound
    (partitionHighestTensor (mu N) (hmu N)) (mu N)
    (partitionHighestTensor_cartan (mu N) (hmu N))
    (partitionHighestTensor_raising_zero (mu N) (hmu N)) a R (hL.trans (hg a))
    ((cyclicCutoff _ _).sub_mem (cutoffFrame_mem _ _ R i) (cutoffRawFrame_mem _ _ R i))

theorem partition_normalizedWord_norm_tendsto (w : List (PositiveRoot d)) :
    Tendsto (fun N => ‖normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N))
      (mu N) w‖) atTop (𝓝 1) := by
  have hg := partition_normalized_gram_tendsto (fun a : PositiveRoot d => a)
    Function.injective_id mu hmu δ hδ hgap w w
  simp only [if_pos (List.Perm.refl w)] at hg
  have h := ((Complex.continuous_re.tendsto 1).comp hg).sqrt
  simpa only [norm_eq_sqrt_re_inner (𝕜 := ℂ), normalizedLoweringWord,
    Function.comp_def, Complex.one_re, Real.sqrt_one] using h

theorem partition_creator_rawFrame_norm_tendsto (a : PositiveRoot d) (R : ℕ)
    (i : CutoffIndex d R) :
    Tendsto (fun N => ‖normalizedCreator (∑ j, mu N j) (mu N) a.val.1 a.val.2
      (cutoffRawFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖)
      atTop (𝓝 (Real.sqrt (((cutoffWord d R i).count a : ℝ)+1))) := by
  have h := (partition_normalizedWord_norm_tendsto mu hmu δ hδ hgap
    (a::cutoffWord d R i)).const_mul (Real.sqrt (((cutoffWord d R i).count a : ℝ)+1))
  simp only [mul_one] at h
  simpa only [cutoffRawFrame, normalizedCreator_normalizedLoweringWord, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h

theorem partition_creator_frame_norm_tendsto (a : PositiveRoot d) (R : ℕ)
    (i : CutoffIndex d R) :
    Tendsto (fun N => ‖normalizedCreator (∑ j, mu N j) (mu N) a.val.1 a.val.2
      (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i)‖)
      atTop (𝓝 (Real.sqrt (((cutoffWord d R i).count a : ℝ)+1))) :=
  varying_norm_tendsto_of_close _ _ _
    (partition_creator_rawFrame_norm_tendsto mu hmu δ hδ hgap a R i)
    (partition_creator_frame_close mu hmu δ hδ hgap a R i)

/-- The creator matrix entries have the correct explicit oscillator limits
in the common GS frame, including repeated Cartan-weight blocks. -/
theorem partition_creator_frame_tendsto (a : PositiveRoot d) (R : ℕ)
    (i j : CutoffIndex d R) :
    Tendsto (fun N =>
      ⟪cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i,
        normalizedCreator (∑ k, mu N k) (mu N) a.val.1 a.val.2
          (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)⟫_ℂ)
      atTop (𝓝 (creationEntry a (cutoffWord d R i) (cutoffWord d R j))) :=
  varying_inner_tendsto_of_two_close _ _ _ _ 1 _ _
    (partition_cutoffFrame_close mu hmu δ hδ hgap R i)
    (partition_creator_frame_close mu hmu δ hδ hgap a R j)
    (partition_cutoffRawFrame_norm_tendsto mu hmu δ hδ hgap R i)
    (partition_creator_frame_norm_tendsto mu hmu δ hδ hgap a R j)
    (partition_creator_word_tendsto mu hmu δ hδ hgap a (cutoffWord d R i) (cutoffWord d R j))

theorem partition_annihilator_frame_tendsto (a : PositiveRoot d) (R : ℕ)
    (i j : CutoffIndex d R) :
    Tendsto (fun N =>
      ⟪cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i,
        normalizedAnnihilator (∑ k, mu N k) (mu N) a.val.1 a.val.2
          (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)⟫_ℂ)
      atTop (𝓝 (annihilationEntry a (cutoffWord d R i) (cutoffWord d R j))) := by
  have hh := (partition_creator_frame_tendsto mu hmu δ hδ hgap a R j i).star
  convert hh using 1
  ext N
  rw [← normalized_inner_adjoint]
  exact (inner_conj_symm _ _).symm

/-- Genuine physical infinitesimal displacements approach the explicit
finite oscillator matrix. The displacement parameters may also vary. -/
theorem partition_rootGenerator_frame_tendsto (z : ℕ → PositiveRoot d → ℂ)
    (z₀ : PositiveRoot d → ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (R : ℕ) (i j : CutoffIndex d R) :
    Tendsto (fun N =>
      ⟪cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R i,
        rootGenerator (mu N) (z N)
          (cutoffFrame (partitionHighestTensor (mu N) (hmu N)) (mu N) R j)⟫_ℂ)
      atTop (𝓝 (oscillatorEntry z₀ (cutoffWord d R i) (cutoffWord d R j))) := by
  simp only [rootGenerator, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sum, inner_sub_right, inner_smul_right, oscillatorEntry]
  apply tendsto_finset_sum
  intro a _
  exact ((tendsto_pi_nhds.mp hz a).mul
    (partition_creator_frame_tendsto mu hmu δ hδ hgap a R i j)).sub
      ((tendsto_pi_nhds.mp hz a).star.mul
        (partition_annihilator_frame_tendsto mu hmu δ hδ hgap a R i j))

end Cloning.TensorLocalUnitary
