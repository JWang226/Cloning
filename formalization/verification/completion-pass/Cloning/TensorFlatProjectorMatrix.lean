import Cloning.TensorFlatProjectorState
import Cloning.TensorCartanTensorAction
import Cloning.MatrixFidelityProjector

/-! Actual matrix coordinates of physical support projections and Cartan covariance. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {d r k : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionActionMatrix (mu : Fin d → ℕ) (hmu : Antitone mu)
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ :=
  LinearMap.toMatrix (partitionBasis mu hmu).toBasis (partitionBasis mu hmu).toBasis
    (partitionTensorAction mu hmu X).toLinearMap

@[simp] theorem partitionActionMatrix_apply (mu : Fin d → ℕ) (hmu : Antitone mu)
    (X : Matrix (Fin d) (Fin d) ℂ) (i j : PartitionIndex mu hmu) :
    partitionActionMatrix mu hmu X i j =
      ⟪partitionBasis mu hmu i, partitionTensorAction mu hmu X (partitionBasis mu hmu j)⟫_ℂ := by
  simp [partitionActionMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

theorem partitionActionMatrix_mul (mu : Fin d → ℕ) (hmu : Antitone mu)
    (X Y : Matrix (Fin d) (Fin d) ℂ) :
    partitionActionMatrix mu hmu (X*Y) = partitionActionMatrix mu hmu X * partitionActionMatrix mu hmu Y := by
  unfold partitionActionMatrix partitionTensorAction
  rw [cyclicTensorOperator_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem partitionActionMatrix_star (mu : Fin d → ℕ) (hmu : Antitone mu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    partitionActionMatrix mu hmu Xᴴ = (partitionActionMatrix mu hmu X)ᴴ := by
  ext i j
  simp only [partitionActionMatrix_apply, Matrix.conjTranspose_apply,
    ← starRingEnd_apply, inner_conj_symm]
  change ⟪(partitionBasis mu hmu i : TensorRegister (∑a,mu a) (Fin d)),
    tensorOperator (∑a,mu a) Xᴴ (partitionBasis mu hmu j : TensorRegister (∑a,mu a) (Fin d))⟫_ℂ =
    ⟪tensorOperator (∑a,mu a) X (partitionBasis mu hmu i : TensorRegister (∑a,mu a) (Fin d)), (partitionBasis mu hmu j : TensorRegister (∑a,mu a) (Fin d))⟫_ℂ
  rw [tensorOperator_star, ContinuousLinearMap.adjoint_inner_right]

theorem cartanProductAction_matrix (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.toMatrix (cartanProductBasis mu nu hmu hnu).toBasis
      (cartanProductBasis mu nu hmu hnu).toBasis (cartanProductAction mu nu hmu hnu X).toLinearMap =
      partitionActionMatrix mu hmu X ⊗ₖ partitionActionMatrix nu hnu X := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    cartanProductBasis, productSectorBasis_apply]
  change ⟪tensorJoin (partitionBasis mu hmu i.1 : TensorRegister (∑a,mu a) (Fin d))
      (partitionBasis nu hnu i.2 : TensorRegister (∑a,nu a) (Fin d)),
    tensorOperator _ X (tensorJoin (partitionBasis mu hmu j.1 : TensorRegister (∑a,mu a) (Fin d))
      (partitionBasis nu hnu j.2 : TensorRegister (∑a,nu a) (Fin d)))⟫_ℂ = _
  rw [tensorOperator_tensorJoin, tensorJoin_inner]
  simp only [Matrix.kroneckerMap_apply, partitionActionMatrix_apply]
  rfl

/-- Exact matrix Cartan covariance, including singular matrices. -/
theorem cartanMatrix_tensorAction (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    cartanMatrix mu nu hmu hnu *
      partitionActionMatrix (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu) X =
    (partitionActionMatrix mu hmu X ⊗ₖ partitionActionMatrix nu hnu X) * cartanMatrix mu nu hmu hnu := by
  rw [← cartanProductAction_matrix]
  simp only [cartanMatrix, partitionActionMatrix, ← LinearMap.toMatrix_comp]
  congr 1
  exact congrArg ContinuousLinearMap.toLinearMap (cartanInclusion_tensorAction mu nu hmu hnu X)

def partitionCoordinateProjection (mu : Fin (r+k) → ℕ) (hmu : Antitone mu) :=
  partitionActionMatrix mu hmu (coordinateSupportMatrix r k)

theorem coordinateSupportMatrix_idempotent :
    coordinateSupportMatrix r k * coordinateSupportMatrix r k = coordinateSupportMatrix r k := by
  rw [coordinateSupportMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp

theorem coordinateSupportMatrix_star : (coordinateSupportMatrix r k)ᴴ = coordinateSupportMatrix r k := by
  simp [coordinateSupportMatrix, Matrix.diagonal_conjTranspose, apply_ite]

theorem partitionCoordinateProjection_idempotent (mu : Fin (r+k) → ℕ) (hmu : Antitone mu) :
    partitionCoordinateProjection mu hmu * partitionCoordinateProjection mu hmu =
      partitionCoordinateProjection mu hmu := by
  exact (partitionActionMatrix_mul mu hmu _ _).symm.trans
    (congrArg (partitionActionMatrix mu hmu) coordinateSupportMatrix_idempotent)

theorem partitionCoordinateProjection_hermitian (mu : Fin (r+k) → ℕ) (hmu : Antitone mu) :
    (partitionCoordinateProjection mu hmu).IsHermitian := by
  exact (partitionActionMatrix_star mu hmu _).symm.trans
    (congrArg (partitionActionMatrix mu hmu) coordinateSupportMatrix_star)

theorem partitionCoordinateProjection_posSemidef (mu : Fin (r+k) → ℕ) (hmu : Antitone mu) :
    (partitionCoordinateProjection mu hmu).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (partitionCoordinateProjection mu hmu)
  rw [(partitionCoordinateProjection_hermitian mu hmu).eq,
    partitionCoordinateProjection_idempotent] at h
  exact h

/-- The coordinate projector has the actual smaller-rank sector dimension. -/
theorem trace_partitionCoordinateProjection_pad (mu : Fin r → ℕ) (hmu : Antitone mu) :
    Matrix.trace (partitionCoordinateProjection (padPartition mu k) (padPartition_antitone mu hmu k)) =
      (partitionDimension mu hmu : ℂ) := by
  rw [partitionCoordinateProjection, partitionActionMatrix, ← LinearMap.trace_eq_matrix_trace]
  exact trace_partitionSupportOperator mu hmu k

end Cloning.TensorLie
