import Cloning.TensorRankOneProduct

/-! Actual one-row Cartan output equals Werner's physical symmetric sandwich. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.TensorCloning Cloning.GeneralSymmetricOccupation Cloning.InfiniteTraceClass
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

section Isometry
variable {H K L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem isometry_comp_adjoint_eq_projection (V : H →ₗᵢ[ℂ] K)
    (S : Submodule ℂ K) [S.HasOrthogonalProjection]
    (hS : V.toLinearMap.range=S) :
    V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint=S.starProjection := by
  apply ContinuousLinearMap.ext
  intro y
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hS]
    exact ⟨_,rfl⟩
  · intro w hw
    rw [← hS] at hw
    obtain ⟨x,rfl⟩ := hw
    rw [inner_sub_left]
    change ⟪y,V x⟫_ℂ-⟪V (V.toContinuousLinearMap.adjoint y),V x⟫_ℂ=0
    rw [LinearIsometry.inner_map_map,ContinuousLinearMap.adjoint_inner_left]
    exact sub_self _

theorem embedded_isometry_compression (V : H →ₗᵢ[ℂ] K) (E : K →ₗᵢ[ℂ] L)
    (B : K →L[ℂ] K) (D : L →L[ℂ] L)
    (hBD : ∀y,E (B y)=D (E y)) :
    let J := (E.comp V).toContinuousLinearMap
    let P := J.comp J.adjoint
    operatorConjugation J (V.toContinuousLinearMap.adjoint.comp (B.comp V.toContinuousLinearMap))=
      P*D*P := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro x
  have hec : (E.comp V).toContinuousLinearMap=E.toContinuousLinearMap.comp V.toContinuousLinearMap := rfl
  rw [hec]
  simp only [operatorConjugation_apply,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply]
  change E (V (V.toContinuousLinearMap.adjoint (B (V (V.toContinuousLinearMap.adjoint
      (E.toContinuousLinearMap.adjoint x))))))=
    E (V (V.toContinuousLinearMap.adjoint (E.toContinuousLinearMap.adjoint
      (D (E (V (V.toContinuousLinearMap.adjoint (E.toContinuousLinearMap.adjoint x))))))))
  rw [← hBD,isometry_adjoint_apply_self]

end Isometry

local instance {n d : ℕ} : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cartanAmbientInclusion_projection_oneRow (n m d : ℕ) :
    let V := (cartanAmbientInclusion (oneRowPartition n d) (oneRowPartition m d)
      (oneRowPartition_antitone n d) (oneRowPartition_antitone m d)).toContinuousLinearMap
    V.comp V.adjoint=physicalProjector ((∑i,oneRowPartition n d i)+∑i,oneRowPartition m d i) :=
  isometry_comp_adjoint_eq_projection _ _ (cartanAmbientInclusion_range_oneRow n m d)

theorem cartan_oneRow_highest_werner (n m d : ℕ) :
    let mu := oneRowPartition n d
    let nu := oneRowPartition m d
    let hm := oneRowPartition_antitone n d
    let hn := oneRowPartition_antitone m d
    conjugationLinearMap (cartanAmbientInclusion mu nu hm hn).toContinuousLinearMap
      ((physicalCartanChannel mu nu hm hn).toLinearMap (vectorProjector (oneRowHighestVector n d)))=
      pureWernerOutput (by simp : Fintype.card (Fin (d+1))=d+1)
        (registerBasis (Fin (d+1)) 0) ((registerBasis _).orthonormal.norm_eq_one _)
        (inputSlots (∑i,mu i) ((∑i,mu i)+∑i,nu i) (Nat.le_add_right _ _)) := by
  dsimp only
  let mu := oneRowPartition n d
  let nu := oneRowPartition m d
  let hm := oneRowPartition_antitone n d
  let hn := oneRowPartition_antitone m d
  let S := tensorProductSector (cyclicSector (partitionHighestTensor mu hm))
    (cyclicSector (partitionHighestTensor nu hn))
  let V := cartanInclusion mu nu hm hn
  let E := S.subtypeₗᵢ
  let B := cartanProductOperator mu nu hm hn (vectorProjector (oneRowHighestVector n d)).1
  let D := fixedSlotProjector (0 : Fin (d+1)) (inputSlots (∑i,mu i) ((∑i,mu i)+∑i,nu i) (Nat.le_add_right _ _))
  have hBD : ∀y,E (B y)=D (E y) := fun y =>
    congrArg (fun T : S →L[ℂ] TensorRegister ((∑i,mu i)+∑i,nu i) (Fin (d+1)) => T y) (cartanProductOperator_oneRow_highest n m d)
  have he0 := embedded_isometry_compression V E B D hBD
  have hp : (E.comp V).toContinuousLinearMap.comp (E.comp V).toContinuousLinearMap.adjoint=
      physicalProjector ((∑i,mu i)+∑i,nu i) := cartanAmbientInclusion_projection_oneRow n m d
  have he := he0.trans (congrArg (fun P : TensorRegister ((∑i,mu i)+∑i,nu i) (Fin (d+1)) →L[ℂ]
      TensorRegister ((∑i,mu i)+∑i,nu i) (Fin (d+1)) => P*D*P) hp)
  have hsum : (fun i=>mu i+nu i)=oneRowPartition (n+m) d := by
    funext i
    dsimp [mu,nu,oneRowPartition]
    split_ifs <;> simp
  have hdim : partitionDimension (fun i=>mu i+nu i) (sumPartition_antitone mu nu hm hn)=
      (n+m+d).choose d := by
    have hreal := partitionDimension_eq_dimensionProduct _ (sumPartition_antitone mu nu hm hn)
    have hprod := congrArg WeylCharacter.dimensionProduct hsum
    exact_mod_cast hreal.trans (hprod.trans (dimensionProduct_oneRow (n+m) d))
  apply Subtype.ext
  change operatorConjugation (cartanAmbientInclusion mu nu hm hn).toContinuousLinearMap
      (((physicalCartanChannel mu nu hm hn).toLinearMap (vectorProjector (oneRowHighestVector n d))).1)=_
  rw [physicalCartanChannel_operator,map_smul]
  change ((partitionDimension mu hm:ℂ)/(partitionDimension _ (sumPartition_antitone mu nu hm hn):ℂ)) •
    operatorConjugation (E.comp V).toContinuousLinearMap
      (V.toContinuousLinearMap.adjoint.comp (B.comp V.toContinuousLinearMap))=_
  rw [he]
  change _=pureWernerOperator d (registerBasis (Fin (d+1)) 0)
    (inputSlots (∑i,mu i) ((∑i,mu i)+∑i,nu i) (Nat.le_add_right _ _))
  rw [pureWernerOperator,pureSlotsOperator_basis_zero,inputSlots_card,hdim]
  have hsource : partitionDimension mu hm=(n+d).choose d := partitionDimension_oneRow n d
  rw [hsource]
  congr 1
  simp only [mu,nu,oneRowPartition_sum]
  push_cast
  rfl

end Cloning.TensorLie
