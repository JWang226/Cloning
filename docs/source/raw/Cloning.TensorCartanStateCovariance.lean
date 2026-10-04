import Cloning.TensorCartanTensorAction
import Cloning.TensorCartanStateProduct
import Cloning.TensorGibbsState

/-! Exact unitary covariance of the literal physical Cartan quantum channel. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cartanProductAction_productVector (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ)
    (x : cyclicSector (partitionHighestTensor mu hmu))
    (y : cyclicSector (partitionHighestTensor nu hnu)) :
    cartanProductAction mu nu hmu hnu X (cartanProductVector mu nu hmu hnu x y) =
      cartanProductVector mu nu hmu hnu (partitionTensorAction mu hmu X x)
        (partitionTensorAction nu hnu X y) := by
  apply Subtype.ext
  exact tensorOperator_tensorJoin X
    (x : TensorRegister (∑ i, mu i) (Fin d)) (y : TensorRegister (∑ i, nu i) (Fin d))

theorem cartanProductOperator_conjugate (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : cyclicSector (partitionHighestTensor mu hmu) →L[ℂ]
      cyclicSector (partitionHighestTensor mu hmu)) :
    cartanProductOperator mu nu hmu hnu
      (partitionTensorAction mu hmu U * A * partitionTensorAction mu hmu Uᴴ) =
      cartanProductAction mu nu hmu hnu U * cartanProductOperator mu nu hmu hnu A *
        cartanProductAction mu nu hmu hnu Uᴴ := by
  have he (i : PartitionIndex mu hmu × PartitionIndex nu hnu) :
      cartanProductOperator mu nu hmu hnu
          (partitionTensorAction mu hmu U * A * partitionTensorAction mu hmu Uᴴ)
          (cartanProductBasis mu nu hmu hnu i) =
        (cartanProductAction mu nu hmu hnu U * cartanProductOperator mu nu hmu hnu A *
          cartanProductAction mu nu hmu hnu Uᴴ) (cartanProductBasis mu nu hmu hnu i) := by
    simp only [cartanProductBasis, productSectorBasis_apply]
    change cartanProductOperator mu nu hmu hnu _
        (cartanProductVector mu nu hmu hnu (partitionBasis mu hmu i.1) (partitionBasis nu hnu i.2)) =
      (cartanProductAction mu nu hmu hnu U * cartanProductOperator mu nu hmu hnu A *
        cartanProductAction mu nu hmu hnu Uᴴ) (cartanProductVector mu nu hmu hnu (partitionBasis mu hmu i.1) (partitionBasis nu hnu i.2))
    simp only [ContinuousLinearMap.mul_apply, cartanProductAction_productVector,
      cartanProductOperator_productVector]
    congr 1
    have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
    have hv := congrArg (fun T ↦ T (partitionBasis nu hnu i.2))
      (cyclicTensorOperator_mul (partitionHighestTensor nu hnu) (fun a ↦ (nu a : ℂ))
        (partitionHighestTensor_cartan nu hnu) (partitionHighestTensor_raising_zero nu hnu) U Uᴴ)
    simpa only [hUU, cyclicTensorOperator_one, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply] using hv
  apply ContinuousLinearMap.ext
  intro z
  rw [← (cartanProductBasis mu nu hmu hnu).sum_repr z]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i hi ↦ congrArg (fun x ↦
    ((cartanProductBasis mu nu hmu hnu).repr z i) • x) (he i))

end Cloning.TensorLie
