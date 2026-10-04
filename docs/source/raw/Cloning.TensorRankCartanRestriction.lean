import Cloning.TensorFlatProjectorProduct
import Cloning.TensorFlatProjectorFidelity
import Cloning.TensorCartanWordSplit

/-! Exact naturality of the physical Cartan inclusion under rank restriction. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def rankSectorEmbeddingMatrix (mu : Fin r→ℕ) (hmu : Antitone mu) (k : ℕ) :
    Matrix (PartitionIndex (padPartition mu k) (padPartition_antitone mu hmu k))
      (PartitionIndex mu hmu) ℂ :=
  LinearMap.toMatrix (partitionBasis mu hmu).toBasis
    (partitionBasis (padPartition mu k) (padPartition_antitone mu hmu k)).toBasis
    (rankSectorEmbedding mu hmu k).toLinearMap

@[simp] theorem rankSectorEmbeddingMatrix_apply (mu : Fin r→ℕ) (hmu : Antitone mu) (k : ℕ)
    (i : PartitionIndex (padPartition mu k) (padPartition_antitone mu hmu k))
    (j : PartitionIndex mu hmu) :
    rankSectorEmbeddingMatrix mu hmu k i j =
      ⟪partitionBasis _ _ i,rankSectorEmbedding mu hmu k (partitionBasis mu hmu j)⟫_ℂ := by
  simp [rankSectorEmbeddingMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.repr_apply_apply]

theorem rankSectorEmbeddingMatrix_isometry (mu : Fin r→ℕ) (hmu : Antitone mu) (k : ℕ) :
    (rankSectorEmbeddingMatrix mu hmu k)ᴴ*rankSectorEmbeddingMatrix mu hmu k=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,rankSectorEmbeddingMatrix_apply,
    ←starRingEnd_apply,inner_conj_symm]
  rw [(partitionBasis _ _).sum_inner_mul_inner,(rankSectorEmbedding mu hmu k).inner_map_map]
  exact orthonormal_iff_ite.mp (partitionBasis mu hmu).orthonormal i j

def partitionSectorCongr {d : ℕ} (mu nu : Fin d→ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (he : mu=nu) : cyclicSector (partitionHighestTensor mu hmu) ≃ₗᵢ[ℂ]
      cyclicSector (partitionHighestTensor nu hnu) := by
  subst nu
  exact LinearIsometryEquiv.refl ℂ _

@[simp] theorem partitionSectorCongr_loweringWord {d : ℕ}
    (mu nu : Fin d→ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (he : mu=nu)
    (w : List (PositiveRoot d)) :
    partitionSectorCongr mu nu hmu hnu he
      ⟨loweringWord (partitionHighestTensor mu hmu) w,loweringWord_mem_cyclicSector _ _⟩ =
      ⟨loweringWord (partitionHighestTensor nu hnu) w,loweringWord_mem_cyclicSector _ _⟩ := by
  subst nu
  rfl

def rankSumSectorEmbedding (mu nu : Fin r→ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    cyclicSector (partitionHighestTensor (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu)) →ₗᵢ[ℂ]
      cyclicSector (partitionHighestTensor (fun a=>padPartition mu k a+padPartition nu k a)
        (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))) :=
  (partitionSectorCongr _ _ (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)
    (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
    (padPartition_add mu nu k)).toLinearIsometry.comp
      (rankSectorEmbedding _ (sumPartition_antitone mu nu hmu hnu) k)

theorem rankSumSectorEmbedding_loweringWord (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) (w : List (PositiveRoot r)) :
    rankSumSectorEmbedding mu nu hmu hnu k
      ⟨loweringWord (partitionHighestTensor (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu)) w,
        loweringWord_mem_cyclicSector _ _⟩ =
      ⟨loweringWord (partitionHighestTensor (fun a=>padPartition mu k a+padPartition nu k a)
        (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)))
        (w.map coordinateRoot),loweringWord_mem_cyclicSector _ _⟩ := by
  have he : rankSectorEmbedding _ (sumPartition_antitone mu nu hmu hnu) k
      ⟨loweringWord (partitionHighestTensor (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu)) w,
        loweringWord_mem_cyclicSector _ _⟩ =
      ⟨loweringWord (partitionHighestTensor (padPartition (fun a=>mu a+nu a) k)
        (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k))
        (w.map coordinateRoot),loweringWord_mem_cyclicSector _ _⟩ :=
    Subtype.ext (rankSectorEmbedding_loweringWord _ (sumPartition_antitone mu nu hmu hnu) k w)
  change partitionSectorCongr _ _ _ _ (padPartition_add mu nu k)
    (rankSectorEmbedding _ (sumPartition_antitone mu nu hmu hnu) k _) = _
  rw [he]
  exact partitionSectorCongr_loweringWord _ _ _ _ _ _

def rankProductSectorEmbedding (mu nu : Fin r→ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :=
  productSectorIsometry _ _ _ _ (partitionBasis mu hmu) (partitionBasis nu hnu)
    (rankSectorEmbedding mu hmu k) (rankSectorEmbedding nu hnu k)

def rankSumSectorEmbeddingMatrix (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :=
  LinearMap.toMatrix (partitionBasis _ (sumPartition_antitone mu nu hmu hnu)).toBasis
    (partitionBasis _ (sumPartition_antitone _ _ (padPartition_antitone mu hmu k)
      (padPartition_antitone nu hnu k))).toBasis
    (rankSumSectorEmbedding mu nu hmu hnu k).toLinearMap

theorem rankProductSectorEmbedding_matrix (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    LinearMap.toMatrix (cartanProductBasis mu nu hmu hnu).toBasis
      (cartanProductBasis _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toBasis
      (rankProductSectorEmbedding mu nu hmu hnu k).toLinearMap =
      rankSectorEmbeddingMatrix mu hmu k ⊗ₖ rankSectorEmbeddingMatrix nu hnu k := by
  ext i j
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
  change ⟪cartanProductBasis _ _ _ _ i,
    productSectorIsometry _ _ _ _ _ _ _ _ (cartanProductBasis mu nu hmu hnu j)⟫_ℂ = _
  simp only [cartanProductBasis,productSectorIsometry_basis]
  simp only [productSectorBasis_apply]
  change ⟪tensorJoin
    (partitionBasis (padPartition mu k) (padPartition_antitone mu hmu k) i.1 : TensorRegister (∑ a,padPartition mu k a) (Fin (r+k)))
    (partitionBasis (padPartition nu k) (padPartition_antitone nu hnu k) i.2 : TensorRegister (∑ a,padPartition nu k a) (Fin (r+k))),
    tensorJoin (rankSectorEmbedding mu hmu k (partitionBasis mu hmu j.1) : TensorRegister (∑ a,padPartition mu k a) (Fin (r+k)))
      (rankSectorEmbedding nu hnu k (partitionBasis nu hnu j.2) : TensorRegister (∑ a,padPartition nu k a) (Fin (r+k)))⟫_ℂ = _
  rw [tensorJoin_inner]
  simp only [Matrix.kroneckerMap_apply,rankSectorEmbeddingMatrix_apply,Submodule.coe_inner]

theorem rankSumSectorEmbeddingMatrix_isometry (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    (rankSumSectorEmbeddingMatrix mu nu hmu hnu k)ᴴ * rankSumSectorEmbeddingMatrix mu nu hmu hnu k=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,rankSumSectorEmbeddingMatrix,
    LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply,←starRingEnd_apply,inner_conj_symm]
  rw [(partitionBasis _ _).sum_inner_mul_inner]
  change ⟪rankSumSectorEmbedding mu nu hmu hnu k (partitionBasis _ _ i),
    rankSumSectorEmbedding mu nu hmu hnu k (partitionBasis _ _ j)⟫_ℂ = _
  rw [(rankSumSectorEmbedding mu nu hmu hnu k).inner_map_map]
  exact orthonormal_iff_ite.mp (partitionBasis _ (sumPartition_antitone mu nu hmu hnu)).orthonormal i j

theorem loweringSplits_map_coordinate (k : ℕ) (w : List (PositiveRoot r)) :
    loweringSplits (w.map (coordinateRoot (k:=k))) =
      (loweringSplits w).map (fun uv => (uv.1.map coordinateRoot,uv.2.map coordinateRoot)) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons,loweringSplits,ih,List.map_append,List.map_map,
      Function.comp_def]

def productLoweringVector (mu nu : Fin r→ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (uv : List (PositiveRoot r) × List (PositiveRoot r)) :
    tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor nu hnu)) :=
  ⟨tensorJoin (loweringWord (partitionHighestTensor mu hmu) uv.1)
    (loweringWord (partitionHighestTensor nu hnu) uv.2),
    tensorJoin_mem_tensorProductSector _ _ (loweringWord_mem_cyclicSector _ _)
      (loweringWord_mem_cyclicSector _ _)⟩

theorem cartanInclusion_loweringWord_sum (mu nu : Fin r→ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (w : List (PositiveRoot r)) :
    cartanInclusion mu nu hmu hnu
      ⟨loweringWord (partitionHighestTensor (fun a=>mu a+nu a)
        (sumPartition_antitone mu nu hmu hnu)) w,loweringWord_mem_cyclicSector _ _⟩ =
      ((loweringSplits w).map (productLoweringVector mu nu hmu hnu)).sum := by
  apply Subtype.ext
  rw [cartanInclusion_loweringWord]
  change _ = (tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
    (cyclicSector (partitionHighestTensor nu hnu))).subtype
      ((loweringSplits w).map (productLoweringVector mu nu hmu hnu)).sum
  rw [map_list_sum,List.map_map]
  exact loweringWord_tensorJoin_split _ _ w

theorem rankProductSectorEmbedding_loweringWord (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) (w : List (PositiveRoot r)) :
    rankProductSectorEmbedding mu nu hmu hnu k
      (cartanInclusion mu nu hmu hnu
        ⟨loweringWord (partitionHighestTensor (fun a=>mu a+nu a)
          (sumPartition_antitone mu nu hmu hnu)) w,loweringWord_mem_cyclicSector _ _⟩) =
      cartanInclusion _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)
        ⟨loweringWord (partitionHighestTensor (fun a=>padPartition mu k a+padPartition nu k a)
          (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)))
          (w.map coordinateRoot),loweringWord_mem_cyclicSector _ _⟩ := by
  rw [cartanInclusion_loweringWord_sum,cartanInclusion_loweringWord_sum,loweringSplits_map_coordinate]
  simp only [map_list_sum,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro uv _
  apply Subtype.ext
  change (productSectorIsometry _ _ _ _ (partitionBasis mu hmu) (partitionBasis nu hnu)
    (rankSectorEmbedding mu hmu k) (rankSectorEmbedding nu hnu k)
    (productLoweringVector mu nu hmu hnu uv) :
      TensorRegister ((∑ a,padPartition mu k a)+(∑ a,padPartition nu k a)) (Fin (r+k))) = _
  rw [show productLoweringVector mu nu hmu hnu uv =
    ⟨tensorJoin (⟨loweringWord (partitionHighestTensor mu hmu) uv.1,loweringWord_mem_cyclicSector _ _⟩ : cyclicSector _)
      (⟨loweringWord (partitionHighestTensor nu hnu) uv.2,loweringWord_mem_cyclicSector _ _⟩ : cyclicSector _),
      tensorJoin_mem_tensorProductSector _ _ (loweringWord_mem_cyclicSector _ _) (loweringWord_mem_cyclicSector _ _)⟩ from rfl]
  rw [productSectorIsometry_tensorJoin,rankSectorEmbedding_loweringWord,rankSectorEmbedding_loweringWord]
  rfl

/-- The actual Cartan inclusion commutes with the physical rank embeddings
on the entire cyclic sector, with the highest-vector phases fixed. -/
theorem rankCartanInclusion_restriction (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    (cartanInclusion _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toLinearMap.comp
      (rankSumSectorEmbedding mu nu hmu hnu k).toLinearMap =
      (rankProductSectorEmbedding mu nu hmu hnu k).toLinearMap.comp
        (cartanInclusion mu nu hmu hnu).toLinearMap := by
  let f := (cartanInclusion _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toLinearMap.comp
      (rankSumSectorEmbedding mu nu hmu hnu k).toLinearMap
  let g := (rankProductSectorEmbedding mu nu hmu hnu k).toLinearMap.comp
        (cartanInclusion mu nu hmu hnu).toLinearMap
  change f=g
  apply LinearMap.ext
  rintro ⟨x,hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    change cartanInclusion _ _ _ _ (rankSumSectorEmbedding mu nu hmu hnu k _) =
      rankProductSectorEmbedding mu nu hmu hnu k (cartanInclusion mu nu hmu hnu _)
    rw [rankSumSectorEmbedding_loweringWord]
    exact (rankProductSectorEmbedding_loweringWord mu nu hmu hnu k w).symm
  | zero => change f 0=g 0; simp
  | add x y hx hy ihx ihy =>
    change f (⟨x,hx⟩+⟨y,hy⟩) = g (⟨x,hx⟩+⟨y,hy⟩)
    simp only [map_add,ihx,ihy]
  | smul c x hx ih =>
    change f (c • (⟨x,hx⟩ : cyclicSector _)) = g (c • (⟨x,hx⟩ : cyclicSector _))
    simp only [map_smul,ih]

/-- Literal coordinate identity needed by arbitrary-input rank compression. -/
theorem rankCartanMatrix_restriction (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    cartanMatrix _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k) *
      rankSumSectorEmbeddingMatrix mu nu hmu hnu k =
      (rankSectorEmbeddingMatrix mu hmu k ⊗ₖ rankSectorEmbeddingMatrix nu hnu k) *
        cartanMatrix mu nu hmu hnu := by
  rw [←rankProductSectorEmbedding_matrix]
  simp only [cartanMatrix,rankSumSectorEmbeddingMatrix,←LinearMap.toMatrix_comp]
  exact congrArg (LinearMap.toMatrix
    (partitionBasis _ (sumPartition_antitone mu nu hmu hnu)).toBasis
    (cartanProductBasis _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toBasis)
    (rankCartanInclusion_restriction mu nu hmu hnu k)

end Cloning.TensorLie
