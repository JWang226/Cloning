import Cloning.TensorRankOneSector
import Cloning.TensorCartanIntertwiner

/-! One-row sectors and their canonical embeddings are independent of the chosen highest phase. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorCloning
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n d : ℕ}

theorem occupancy_eq_length_iff_constant (w : Fin n → Fin (d+1)) (a : Fin (d+1)) :
    occupancy w a=n ↔ w=(fun _=>a) := by
  simpa only [Finset.card_univ,Fintype.card_fin,Finset.mem_univ,true_implies,
    funext_iff,occupancy] using
    (Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin n))) (p := fun i=>w i=a))

theorem top_occupation_eq_smul_highest (Ω : TensorRegister n (Fin (d+1)))
    (hΩ : collectiveGenerator n 0 0 Ω=(n:ℂ) • Ω) :
    Ω=Ω (fun _=>0) • highestTensor n d := by
  ext w
  have he := congrArg (fun x : TensorRegister n (Fin (d+1)) => x w) hΩ
  simp only [collectiveGenerator_diagonal,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] at he
  by_cases hw : w=(fun _=>0)
  · subst w
    simp [highestTensor,registerBasis_apply,lp.single_apply,Pi.single_apply]
  · have hne : occupancy w 0 ≠ n := mt (occupancy_eq_length_iff_constant w 0).mp hw
    have hn : (occupancy w 0 : ℂ) ≠ n := by exact_mod_cast hne
    have hz : Ω w=0 := (mul_eq_mul_right_iff.mp he).resolve_left hn
    simp [highestTensor,registerBasis_apply,lp.single_apply,Pi.single_apply,hw,hz]

theorem loweringWord_smul_highest (Ω : TensorRegister n (Fin d)) (c : ℂ)
    (w : List (PositiveRoot d)) : loweringWord (c • Ω) w=c • loweringWord Ω w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [loweringWord,ih,map_smul]

theorem cyclicSector_smul_highest (Ω : TensorRegister n (Fin d)) (c : ℂ) (hc : c≠0) :
    cyclicSector (c • Ω)=cyclicSector Ω := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w,rfl⟩
    rw [loweringWord_smul_highest]
    exact (cyclicSector Ω).smul_mem c (loweringWord_mem_cyclicSector Ω w)
  · apply Submodule.span_le.mpr
    rintro x ⟨w,rfl⟩
    have hh := (cyclicSector (c • Ω)).smul_mem c⁻¹ (loweringWord_mem_cyclicSector (c • Ω) w)
    simpa only [loweringWord_smul_highest,smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

theorem cyclicSector_eq_physicalSymmetric_of_top_occupation
    (Ω : TensorRegister n (Fin (d+1))) (hΩnorm : ‖Ω‖=1)
    (hΩ : collectiveGenerator n 0 0 Ω=(n:ℂ) • Ω) :
    cyclicSector Ω=physicalSymmetric n := by
  have he := top_occupation_eq_smul_highest Ω hΩ
  have hc : Ω (fun _=>0) ≠ 0 := by
    intro hc
    rw [hc,zero_smul] at he
    rw [he,norm_zero] at hΩnorm
    exact zero_ne_one hΩnorm
  calc
    cyclicSector Ω=cyclicSector (Ω (fun _=>0) • highestTensor n d) := congrArg cyclicSector he
    _=cyclicSector (highestTensor n d) := cyclicSector_smul_highest _ _ hc
    _=physicalSymmetric n := cyclicSector_highestTensor_eq_physicalSymmetric n d

theorem canonical_oneRow_sector_eq (n d : ℕ) :
    cyclicSector (partitionHighestTensor (oneRowPartition n d) (oneRowPartition_antitone n d))=
      physicalSymmetric (∑ i,oneRowPartition n d i) := by
  apply cyclicSector_eq_physicalSymmetric_of_top_occupation
    _ (partitionHighestTensor_norm _ _)
  have h := partitionHighestTensor_cartan (oneRowPartition n d) (oneRowPartition_antitone n d) 0
  exact h.trans (by congr 1; simp [oneRowPartition_sum,oneRowPartition])

theorem cartanAmbientInclusion_range_oneRow (n m d : ℕ) :
    LinearMap.range (cartanAmbientInclusion (oneRowPartition n d) (oneRowPartition m d)
      (oneRowPartition_antitone n d) (oneRowPartition_antitone m d)).toLinearMap=
      physicalSymmetric ((∑i,oneRowPartition n d i)+∑i,oneRowPartition m d i) := by
  rw [cartanAmbientInclusion_range]
  apply cyclicSector_eq_physicalSymmetric_of_top_occupation
    _ (cartanHighest_norm _ _ _ _)
  have h := cartanHighest_cartan (oneRowPartition n d) (oneRowPartition m d)
    (oneRowPartition_antitone n d) (oneRowPartition_antitone m d) 0
  exact h.trans (by congr 1; simp [oneRowPartition_sum,oneRowPartition])

end Cloning.TensorLie
