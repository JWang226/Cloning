import Cloning.TensorRankOneCopy
import Cloning.TensorCloningTransitionCovariance
import Cloning.TensorRankOneCoupling

/-! Every physical one-row copy transition gives the same Werner output. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorCloning Cloning.InfiniteTraceClass Cloning.TensorLAN Cloning.GeneralSymmetricOccupation
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance {n d : ℕ} : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem partitionTransition_singleRow_highest_werner
    (D n m L : ℕ) (hD : 0<D) (mu nu : Fin D→ℕ) (hm : Antitone mu) (hn : Antitone nu)
    (hmu : ∀i,mu i=if i.val=0 then n else 0)
    (hnu : ∀i,nu i=if i.val=0 then m else 0) (hnm : n≤m)
    (hL : (∑i,nu i)=L) (hsize : (∑i,mu i)≤L)
    (Ψ : TensorRegister L (Fin D)) (hΨ : ‖Ψ‖=1)
    (htΨ : collectiveGenerator L ⟨0,hD⟩ ⟨0,hD⟩ Ψ=(L:ℂ) • Ψ)
    (F : cyclicSector (partitionHighestTensor nu hn) →ₗᵢ[ℂ] TensorRegister L (Fin D))
    (hF : ∀w,F ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩=loweringWord Ψ w) :
    conjugationLinearMap F.toContinuousLinearMap
      ((partitionTransitionChannel mu nu hm hn).toLinearMap
        (vectorProjector ⟨partitionHighestTensor mu hm,highest_mem_cyclicSector _⟩))=
      pureWernerOutput (s:=D-1) (by simp; omega : Fintype.card (Fin D)=(D-1)+1)
        (registerBasis (Fin D) ⟨0,hD⟩) ((registerBasis _).orthonormal.norm_eq_one _)
        (inputSlots (∑i,mu i) L hsize) := by
  let tau : Fin D→ℕ := fun i=>nu i-mu i
  have htau (i : Fin D) : tau i=if i.val=0 then m-n else 0 := by
    dsimp only [tau]
    rw [hmu,hnu]
    split_ifs <;> simp
  have hrow : ∀i,mu i≤nu i := by
    intro i
    rw [hmu,hnu]
    split_ifs <;> omega
  have hata : Antitone tau := by
    intro i j hij
    rw [htau,htau]
    split_ifs with hj hi hi
    · exact le_refl _
    · have : i.val=0 := by have := Fin.le_iff_val_le_val.mp hij; omega
      contradiction
    · exact Nat.zero_le _
    · exact le_refl _
  have he : (fun i=>mu i+tau i)=nu := funext fun i=>Nat.add_sub_of_le (hrow i)
  let P (v : {v : Fin D→ℕ // Antitone v}) : Prop :=
    ∀ (L : ℕ) (hL : (∑i,v.val i)=L) (hsize : (∑i,mu i)≤L)
      (Ψ : TensorRegister L (Fin D)) (hΨ : ‖Ψ‖=1)
      (htΨ : collectiveGenerator L ⟨0,hD⟩ ⟨0,hD⟩ Ψ=(L:ℂ) • Ψ)
      (F : cyclicSector (partitionHighestTensor v.val v.property) →ₗᵢ[ℂ] TensorRegister L (Fin D))
      (hF : ∀w,F ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩=loweringWord Ψ w),
      conjugationLinearMap F.toContinuousLinearMap
        ((partitionTransitionChannel mu v.val hm v.property).toLinearMap
          (vectorProjector ⟨partitionHighestTensor mu hm,highest_mem_cyclicSector _⟩))=
        pureWernerOutput (s:=D-1) (by simp; omega : Fintype.card (Fin D)=(D-1)+1)
          (registerBasis (Fin D) ⟨0,hD⟩) ((registerBasis _).orthonormal.norm_eq_one _)
          (inputSlots (∑i,mu i) L hsize)
  have hbase : P ⟨fun i=>mu i+tau i,sumPartition_antitone mu tau hm hata⟩ := by
    intro L hL hsize Ψ hΨ htΨ F hF
    dsimp only at hL
    rw [Finset.sum_add_distrib] at hL
    subst L
    rw [partitionTransitionChannel_add]
    exact cartan_singleRow_highest_werner_of_wordmap D n (m-n) hD mu tau hm hata
      hmu htau Ψ hΨ htΨ F hF
  have hab : (⟨fun i=>mu i+tau i,sumPartition_antitone mu tau hm hata⟩ :
      {v : Fin D→ℕ // Antitone v})=⟨nu,hn⟩ := Subtype.ext he
  exact (Eq.mp (congrArg P hab) hbase) L hL hsize Ψ hΨ htΨ F hF

theorem canonicalEmbedding_loweringWord {N D : ℕ} (H : PhysicalHighestTensor N D)
    (w : List (PositiveRoot D)) :
    H.canonicalEmbedding ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩=
      loweringWord H.vector w := by
  change (H.canonicalIsometry ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩ :
    TensorRegister N (Fin D))=loweringWord H.vector w
  exact highestCyclicIsometry_loweringWord
    (partitionHighestTensor H.weight H.weight_antitone) H.vector (fun i=>(H.weight i:ℂ))
    (partitionHighestTensor_cartan H.weight H.weight_antitone) H.cartan
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone) H.raising
    (partitionHighestTensor_norm H.weight H.weight_antitone) H.norm_one w

theorem physical_singleRow_transition_highest_werner {n m D : ℕ}
    (hD : 0<D) (H : PhysicalHighestTensor n D) (K : PhysicalHighestTensor m D)
    (hH : ∀i,H.weight i=if i.val=0 then n else 0)
    (hK : ∀i,K.weight i=if i.val=0 then m else 0) (hnm : n≤m) :
    conjugationLinearMap K.canonicalEmbedding.toContinuousLinearMap
      ((partitionTransitionChannel H.weight K.weight H.weight_antitone K.weight_antitone).toLinearMap
        (vectorProjector (⟨partitionHighestTensor H.weight H.weight_antitone,
          highest_mem_cyclicSector _⟩ : H.CanonicalSector)))=
      pureWernerOutput (s:=D-1) (by simp; omega : Fintype.card (Fin D)=(D-1)+1)
        (registerBasis (Fin D) ⟨0,hD⟩) ((registerBasis _).orthonormal.norm_eq_one _)
        (inputSlots n m hnm) := by
  have htop : collectiveGenerator m ⟨0,hD⟩ ⟨0,hD⟩ K.vector=(m:ℂ) • K.vector := by
    simpa only [hK,ite_true] using K.cartan ⟨0,hD⟩
  have hh := partitionTransition_singleRow_highest_werner D n m m hD H.weight K.weight
    H.weight_antitone K.weight_antitone hH hK hnm K.weight_sum
    (by simpa only [H.weight_sum] using hnm) K.vector K.norm_one htop K.canonicalEmbedding
    (canonicalEmbedding_loweringWord K)
  simpa only [H.weight_sum] using hh

theorem copyTransition_oneRow_highest_werner {n m k : ℕ}
    (i : SchurCopy n (1+k)) (j : SchurCopy m (1+k)) (hnm : n≤m)
    (hi : ((recursivePhysicalDecomposition n (1+k)).get i).weight=
      padPartition (fun _ : Fin 1=>n) k)
    (hj : ((recursivePhysicalDecomposition m (1+k)).get j).weight=
      padPartition (fun _ : Fin 1=>m) k) :
    (copyTransition n m (1+k) i j).toLinearMap
      (vectorProjector (⟨partitionHighestTensor
        ((recursivePhysicalDecomposition n (1+k)).get i).weight
        ((recursivePhysicalDecomposition n (1+k)).get i).weight_antitone,
        highest_mem_cyclicSector _⟩ : ((recursivePhysicalDecomposition n (1+k)).get i).CanonicalSector))=
      pureWernerOutput (s:=k) (by simp; omega : Fintype.card (Fin (1+k))=k+1)
        (registerBasis (Fin (1+k)) 0) ((registerBasis _).orthonormal.norm_eq_one _)
        (inputSlots n m hnm) := by
  have hrow (N : ℕ) (a : Fin (1+k)) : padPartition (fun _ : Fin 1=>N) k a=
      if a.val=0 then N else 0 := by
    induction a using Fin.addCases with
    | left a =>
      rw [padPartition_left]
      have ha : a.val=0 := by omega
      simp only [Fin.val_castAdd,ha,ite_true]
    | right a =>
      rw [padPartition_right]
      simp only [Fin.val_natAdd]
      rw [if_neg (by omega)]
  simpa only [copyTransition,QuantumChannel.comp,QuantumChannel.ofIsometry,
    PositiveTracePreservingMap.comp,LinearMap.comp_apply,Nat.add_sub_cancel_left] using
    physical_singleRow_transition_highest_werner (n:=n) (m:=m) (D:=1+k) (by omega)
    ((recursivePhysicalDecomposition n (1+k)).get i)
    ((recursivePhysicalDecomposition m (1+k)).get j)
    (fun a=>by rw [hi,hrow]) (fun a=>by rw [hj,hrow]) hnm

end Cloning.TensorLie
