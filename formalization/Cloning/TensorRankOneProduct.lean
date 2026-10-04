import Cloning.TensorRankOneHighest
import Cloning.TensorCartanStateProduct
import Cloning.PCTCoordinateFrame
import Cloning.PCTGaussianAssembly

/-! The first-factor highest projector is the literal fixed-input-slot operator. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorCloning Cloning.GeneralSymmetricOccupation Cloning.InfiniteTraceClass
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

local instance {n d : ℕ} : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem rankOne_top_occupation {n d : ℕ} (Ω : TensorRegister n (Fin (d+1)))
    (hnorm : ‖Ω‖=1) (htop : collectiveGenerator n 0 0 Ω=(n:ℂ) • Ω) :
    InnerProductSpace.rankOne ℂ Ω Ω=InnerProductSpace.rankOne ℂ (highestTensor n d) (highestTensor n d) := by
  let c := Ω (fun _=>0)
  have he : Ω=c • highestTensor n d := top_occupation_eq_smul_highest Ω htop
  have hcc : star c*c=1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Ω
    rw [hnorm] at h
    rw [he,inner_smul_left,inner_smul_right,
      inner_self_eq_norm_sq_to_K,highestTensor_norm] at h
    norm_num only [one_pow,map_one,mul_one,starRingEnd_apply] at h
    exact h
  apply ContinuousLinearMap.ext
  intro x
  rw [he]
  simp only [InnerProductSpace.rankOne_apply,inner_smul_left,smul_smul,starRingEnd_apply]
  have hc (a : ℂ) : (star c*a)*c=a := by rw [mul_right_comm,hcc,one_mul]
  rw [hc]

theorem inputSlots_subset_letterSlots_iff {n m d : ℕ} (w : Fin (n+m) → Fin (d+1)) :
    inputSlots n (n+m) (Nat.le_add_right n m) ⊆ letterSlots w 0 ↔
      (fun i : Fin n => w (Fin.castAdd m i))=(fun _=>0) := by
  simp only [Finset.subset_iff,mem_inputSlots,mem_letterSlots,funext_iff]
  constructor
  · intro h i
    exact h i.isLt
  · intro h i hi
    have he : Fin.castAdd m (⟨i.val,hi⟩ : Fin n)=i := Fin.ext rfl
    rw [← he]
    exact h _

theorem fixedSlotProjector_tensorJoin {n m d : ℕ}
    (x : TensorRegister n (Fin (d+1))) (y : TensorRegister m (Fin (d+1))) :
    fixedSlotProjector 0 (inputSlots n (n+m) (Nat.le_add_right n m)) (tensorJoin x y)=
      tensorJoin (InnerProductSpace.rankOne ℂ (highestTensor n d) (highestTensor n d) x) y := by
  ext w
  simp only [fixedSlotProjector_apply,inputSlots_subset_letterSlots_iff]
  simp only [tensorJoin_apply,InnerProductSpace.rankOne_apply,highestTensor,registerBasis_apply,
    lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_apply]
  split_ifs with hw
  · rw [hw]
    simp
  · simp

theorem pureSlotsOperator_basis_zero {L d : ℕ} (S : Finset (Fin L)) :
    pureSlotsOperator (registerBasis (Fin (d+1)) 0) S=fixedSlotProjector 0 S := by
  have h := tensorFrame_fixedSlot_physical
    (Cloning.PCTGlobal.coordinateFrame (Equiv.refl (Fin (d+1)))) 0 S
  simp only [Cloning.PCTGlobal.coordinateFrame_apply,Equiv.refl_apply] at h
  rw [← h]
  apply register_operator_ext
  intro a b
  exact (Cloning.PCTGlobal.coordinate_operator_coefficient (Equiv.refl (Fin (d+1))) L
    (fixedSlotProjector 0 S) a b)

def oneRowHighestVector (n d : ℕ) :
    cyclicSector (partitionHighestTensor (oneRowPartition n d) (oneRowPartition_antitone n d)) :=
  ⟨partitionHighestTensor _ _,highest_mem_cyclicSector _⟩

theorem oneRowHighest_rankOne_apply (n d : ℕ)
    (x : cyclicSector (partitionHighestTensor (oneRowPartition n d) (oneRowPartition_antitone n d))) :
    ((vectorProjector (oneRowHighestVector n d)).1 x :
      TensorRegister (∑i,oneRowPartition n d i) (Fin (d+1)))=
      InnerProductSpace.rankOne ℂ (highestTensor (∑i,oneRowPartition n d i) d)
        (highestTensor (∑i,oneRowPartition n d i) d) x.val := by
  have ht : collectiveGenerator (∑i,oneRowPartition n d i) 0 0
      (partitionHighestTensor (oneRowPartition n d) (oneRowPartition_antitone n d))=
      ((∑i,oneRowPartition n d i : ℕ):ℂ) • partitionHighestTensor _ _ :=
    (partitionHighestTensor_cartan _ _ 0).trans (by congr 1; simp [oneRowPartition])
  exact congrArg (fun T => T (x : TensorRegister (∑i,oneRowPartition n d i) (Fin (d+1))))
    (rankOne_top_occupation _ (partitionHighestTensor_norm _ _) ht)

theorem cartanProductOperator_oneRow_highest (n m d : ℕ) :
    let mu := oneRowPartition n d
    let nu := oneRowPartition m d
    let hm := oneRowPartition_antitone n d
    let hn := oneRowPartition_antitone m d
    let S := tensorProductSector (cyclicSector (partitionHighestTensor mu hm))
      (cyclicSector (partitionHighestTensor nu hn))
    S.subtypeL.comp (cartanProductOperator mu nu hm hn (vectorProjector (oneRowHighestVector n d)).1)=
      (fixedSlotProjector 0 (inputSlots (∑i,mu i) ((∑i,mu i)+∑i,nu i) (Nat.le_add_right _ _))).comp
        S.subtypeL := by
  dsimp only
  apply ContinuousLinearMap.coe_injective
  apply (cartanProductBasis _ _ _ _).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis,cartanProductBasis,productSectorBasis_apply,
    ContinuousLinearMap.comp_apply]
  change (cartanProductOperator _ _ _ _ _ (cartanProductVector _ _ _ _
    (partitionBasis _ _ i.1) (partitionBasis _ _ i.2))).val=_
  rw [cartanProductOperator_productVector]
  change tensorJoin ((vectorProjector (oneRowHighestVector n d)).1 (partitionBasis _ _ i.1)).val
    (partitionBasis _ _ i.2).val=_
  rw [oneRowHighest_rankOne_apply]
  exact (fixedSlotProjector_tensorJoin _ _).symm

end Cloning.TensorLie
