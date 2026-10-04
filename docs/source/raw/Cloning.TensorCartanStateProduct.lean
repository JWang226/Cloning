import Cloning.TensorCartanStateOperator

/-! The product operator in the actual Cartan channel acts on its first factor. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def cartanProductVector (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (x : cyclicSector (partitionHighestTensor mu hmu))
    (y : cyclicSector (partitionHighestTensor nu hnu)) :
    tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor nu hnu)) :=
  ⟨tensorJoin x y, tensorJoin_mem_tensorProductSector _ _ x.property y.property⟩

theorem cartanProductVector_inner
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (x u : cyclicSector (partitionHighestTensor mu hmu))
    (y v : cyclicSector (partitionHighestTensor nu hnu)) :
    ⟪cartanProductVector mu nu hmu hnu x y, cartanProductVector mu nu hmu hnu u v⟫_ℂ =
      ⟪x,u⟫_ℂ * ⟪y,v⟫_ℂ := by
  change ⟪tensorJoin (x : TensorRegister (∑ a, mu a) (Fin d))
    (y : TensorRegister (∑ a, nu a) (Fin d)),
    tensorJoin (u : TensorRegister (∑ a, mu a) (Fin d))
      (v : TensorRegister (∑ a, nu a) (Fin d))⟫_ℂ = _
  rw [tensorJoin_inner]
  rfl

theorem cartanProductBasis_inner_productVector
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (x : cyclicSector (partitionHighestTensor mu hmu))
    (y : cyclicSector (partitionHighestTensor nu hnu))
    (i : PartitionIndex mu hmu × PartitionIndex nu hnu) :
    ⟪cartanProductBasis mu nu hmu hnu i, cartanProductVector mu nu hmu hnu x y⟫_ℂ =
      ⟪partitionBasis mu hmu i.1,x⟫_ℂ * ⟪partitionBasis nu hnu i.2,y⟫_ℂ := by
  simp only [cartanProductBasis, productSectorBasis_apply]
  change ⟪cartanProductVector mu nu hmu hnu (partitionBasis mu hmu i.1)
      (partitionBasis nu hnu i.2), cartanProductVector mu nu hmu hnu x y⟫_ℂ = _
  exact cartanProductVector_inner mu nu hmu hnu _ _ _ _

theorem cartanProductOperator_productVector
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (A : cyclicSector (partitionHighestTensor mu hmu) →L[ℂ]
      cyclicSector (partitionHighestTensor mu hmu))
    (x : cyclicSector (partitionHighestTensor mu hmu))
    (y : cyclicSector (partitionHighestTensor nu hnu)) :
    cartanProductOperator mu nu hmu hnu A (cartanProductVector mu nu hmu hnu x y) =
      cartanProductVector mu nu hmu hnu (A x) y := by
  apply (cartanProductBasis mu nu hmu hnu).repr.injective
  ext ⟨i,j⟩
  simp only [OrthonormalBasis.repr_apply_apply, cartanProductOperator,
    inner_ofMatrix_apply (cartanProductBasis mu nu hmu hnu).orthonormal,
    cartanProductBasis_inner_productVector, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, matrixOf, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h := congrArg (fun z => ⟪partitionBasis mu hmu i, A z⟫_ℂ)
    ((partitionBasis mu hmu).sum_repr x)
  simp only [map_sum, map_smul, inner_sum, inner_smul_right,
    OrthonormalBasis.repr_apply_apply] at h
  calc
    _ = (∑ l, ⟪partitionBasis mu hmu l,x⟫_ℂ * ⟪partitionBasis mu hmu i,A (partitionBasis mu hmu l)⟫_ℂ) *
        ⟪partitionBasis nu hnu j,y⟫_ℂ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [h]

theorem cartanProductVector_smul_left
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (c : ℂ) (x : cyclicSector (partitionHighestTensor mu hmu))
    (y : cyclicSector (partitionHighestTensor nu hnu)) :
    cartanProductVector mu nu hmu hnu (c • x) y =
      c • cartanProductVector mu nu hmu hnu x y := by
  apply Subtype.ext
  exact tensorJoin_smul_left _ _ _

theorem cartanInclusion_cutoff_product_expansion
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (R : ℕ)
    (hmuGap : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnuGap : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (hmuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor mu hmu) mu R))
    (hnuLI : LinearIndependent ℂ (cutoffRawFrame (partitionHighestTensor nu hnu) nu R))
    (i : CutoffIndex d R) :
    cartanInclusion mu nu hmu hnu
      (cutoffSectorFrame (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))
        (fun a => mu a + nu a) R i) =
      ∑ j : CutoffIndex d R, ∑ k : CutoffIndex d R,
        cartanCutoffFrameMatrixElement mu nu hmu hnu R i j k •
          cartanProductVector mu nu hmu hnu
            (cutoffSectorFrame (partitionHighestTensor mu hmu) mu R j)
            (cutoffSectorFrame (partitionHighestTensor nu hnu) nu R k) := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact cartanCutoffFrame_product_expansion mu nu hmu hnu R hmuGap hnuGap hmuLI hnuLI i

end Cloning.TensorLie
