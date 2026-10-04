import Cloning.TensorRankOneCartan
import Cloning.TensorRankOnePhase

/-! The Werner identity holds in every physical one-row copy, independently of its phase. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorCloning Cloning.GeneralSymmetricOccupation Cloning.InfiniteTraceClass
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

local instance {n d : ℕ} : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cartan_oneRow_highest_werner_of_wordmap (n m d : ℕ)
    (Ψ : TensorRegister ((∑i,oneRowPartition n d i)+∑i,oneRowPartition m d i) (Fin (d+1)))
    (hΨ : ‖Ψ‖=1)
    (htΨ : collectiveGenerator _ 0 0 Ψ=
      (((∑i,oneRowPartition n d i)+∑i,oneRowPartition m d i : ℕ):ℂ) • Ψ)
    (F : cyclicSector (partitionHighestTensor (fun i=>oneRowPartition n d i+oneRowPartition m d i)
      (sumPartition_antitone _ _ (oneRowPartition_antitone n d) (oneRowPartition_antitone m d))) →ₗᵢ[ℂ]
      TensorRegister ((∑i,oneRowPartition n d i)+∑i,oneRowPartition m d i) (Fin (d+1)))
    (hF : ∀w,F ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩=loweringWord Ψ w) :
    conjugationLinearMap F.toContinuousLinearMap
      ((physicalCartanChannel (oneRowPartition n d) (oneRowPartition m d)
        (oneRowPartition_antitone n d) (oneRowPartition_antitone m d)).toLinearMap
          (vectorProjector (oneRowHighestVector n d)))=
      pureWernerOutput (by simp : Fintype.card (Fin (d+1))=d+1)
        (registerBasis (Fin (d+1)) 0) ((registerBasis _).orthonormal.norm_eq_one _)
        (inputSlots (∑i,oneRowPartition n d i)
          ((∑i,oneRowPartition n d i)+∑i,oneRowPartition m d i) (Nat.le_add_right _ _)) := by
  let mu := oneRowPartition n d
  let nu := oneRowPartition m d
  let hm := oneRowPartition_antitone n d
  let hn := oneRowPartition_antitone m d
  have htΞ : collectiveGenerator _ 0 0 (cartanHighest mu nu hm hn)=
      (((∑i,mu i)+∑i,nu i : ℕ):ℂ) • cartanHighest mu nu hm hn :=
    (cartanHighest_cartan mu nu hm hn 0).trans (by congr 1; simp [mu,nu,oneRowPartition])
  have hG (w : List (PositiveRoot (d+1))) :
      cartanAmbientInclusion mu nu hm hn ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩=
        loweringWord (cartanHighest mu nu hm hn) w := cartanInclusion_loweringWord mu nu hm hn w
  exact (cyclic_word_isometries_conjugation_eq _ Ψ (cartanHighest mu nu hm hn)
    hΨ (cartanHighest_norm mu nu hm hn) htΨ htΞ F (cartanAmbientInclusion mu nu hm hn) hF hG _).trans
      (cartan_oneRow_highest_werner n m d)

/-- Positive ambient dimension and literal single-row weights permit direct use
with the rank-one zero-padding convention `Fin (1+k)`. -/
theorem cartan_singleRow_highest_werner_of_wordmap
    (D n m : ℕ) (hD : 0<D) (mu nu : Fin D→ℕ) (hm : Antitone mu) (hn : Antitone nu)
    (hmu : ∀i,mu i=if i.val=0 then n else 0)
    (hnu : ∀i,nu i=if i.val=0 then m else 0)
    (Ψ : TensorRegister ((∑i,mu i)+∑i,nu i) (Fin D)) (hΨ : ‖Ψ‖=1)
    (htΨ : collectiveGenerator _ ⟨0,hD⟩ ⟨0,hD⟩ Ψ=(((∑i,mu i)+∑i,nu i : ℕ):ℂ) • Ψ)
    (F : cyclicSector (partitionHighestTensor (fun i=>mu i+nu i) (sumPartition_antitone mu nu hm hn)) →ₗᵢ[ℂ]
      TensorRegister ((∑i,mu i)+∑i,nu i) (Fin D))
    (hF : ∀w,F ⟨loweringWord _ w,loweringWord_mem_cyclicSector _ w⟩=loweringWord Ψ w) :
    conjugationLinearMap F.toContinuousLinearMap
      ((physicalCartanChannel mu nu hm hn).toLinearMap
        (vectorProjector ⟨partitionHighestTensor mu hm,highest_mem_cyclicSector _⟩))=
      pureWernerOutput (s := D-1) (by simp; omega : Fintype.card (Fin D)=(D-1)+1)
        (registerBasis (Fin D) ⟨0,hD⟩) ((registerBasis _).orthonormal.norm_eq_one _)
        (inputSlots (∑i,mu i) ((∑i,mu i)+∑i,nu i) (Nat.le_add_right _ _)) := by
  cases D with
  | zero => omega
  | succ d =>
    have heMu : mu=oneRowPartition n d := by
      funext i
      rw [hmu]
      simp only [oneRowPartition,Fin.ext_iff,Fin.val_zero]
    have heNu : nu=oneRowPartition m d := by
      funext i
      rw [hnu]
      simp only [oneRowPartition,Fin.ext_iff,Fin.val_zero]
    subst mu
    subst nu
    exact cartan_oneRow_highest_werner_of_wordmap n m d Ψ hΨ htΨ F hF

end Cloning.TensorLie
