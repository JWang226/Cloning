import Cloning.PCTRankPurificationSectors
import Cloning.TensorFlatProjectorMatrix
import Cloning.PCTRankPurificationMoment

/-! Literal coordinate matrices for the induced ambient sector family. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
variable {n d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def PhysicalHighestTensor.embeddingMatrix (H : PhysicalHighestTensor n d) :
    Matrix (Fin n → Fin d) (PartitionIndex H.weight H.weight_antitone) ℂ :=
  LinearMap.toMatrix (partitionBasis H.weight H.weight_antitone).toBasis
    (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis H.canonicalEmbedding.toLinearMap

@[simp] theorem PhysicalHighestTensor.embeddingMatrix_apply (H : PhysicalHighestTensor n d)
    (w : Fin n → Fin d) (a : PartitionIndex H.weight H.weight_antitone) :
    H.embeddingMatrix w a=H.canonicalEmbedding (partitionBasis H.weight H.weight_antitone a) w := by
  simp [PhysicalHighestTensor.embeddingMatrix,LinearMap.toMatrix_apply,
    OrthonormalBasis.repr_apply_apply,registerBasis_apply,register_inner_single]

theorem PhysicalHighestTensor.embeddingMatrix_isometry (H : PhysicalHighestTensor n d) :
    H.embeddingMatrixᴴ*H.embeddingMatrix=1 := by
  ext a b
  have he := H.canonicalEmbedding.inner_map_map
    (partitionBasis H.weight H.weight_antitone a) (partitionBasis H.weight H.weight_antitone b)
  rw [orthonormal_iff_ite.mp (partitionBasis _ _).orthonormal] at he
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,PhysicalHighestTensor.embeddingMatrix_apply,
    lp.inner_eq_tsum,tsum_fintype,RCLike.inner_apply,Matrix.one_apply,starRingEnd_apply,mul_comm] using he

theorem toMatrix_tensorOperator (n d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.toMatrix (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis
      (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis (tensorOperator n X).toLinearMap =
      tensorPower n X := by
  ext w v
  simp [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply,OrthonormalBasis.coe_toBasis,
    registerBasis_apply,register_inner_single,tensorOperator_apply,lp.single_apply,Pi.single_apply,tensorPower]

/-- Every induced ambient copy carries the literal canonical matrix action. -/
theorem PhysicalHighestTensor.embeddingMatrix_intertwines (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorPower n X*H.embeddingMatrix=H.embeddingMatrix*partitionActionMatrix H.weight H.weight_antitone X := by
  rw [← toMatrix_tensorOperator]
  unfold PhysicalHighestTensor.embeddingMatrix partitionActionMatrix
  rw [← LinearMap.toMatrix_comp,← LinearMap.toMatrix_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact (H.canonicalEmbedding_tensorOperator X x).symm

def rankSectorMatrix (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    Matrix (PartitionIndex (padPartition mu k) (padPartition_antitone mu hmu k))
      (PartitionIndex mu hmu) ℂ :=
  LinearMap.toMatrix (partitionBasis mu hmu).toBasis
    (partitionBasis (padPartition mu k) (padPartition_antitone mu hmu k)).toBasis
    (rankSectorEmbedding mu hmu k).toLinearMap

@[simp] theorem rankSectorMatrix_apply (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (a : PartitionIndex (padPartition mu k) (padPartition_antitone mu hmu k)) (b : PartitionIndex mu hmu) :
    rankSectorMatrix mu hmu k a b=⟪partitionBasis _ _ a,rankSectorEmbedding mu hmu k (partitionBasis mu hmu b)⟫_ℂ := by
  simp [rankSectorMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.repr_apply_apply]

theorem rankSectorMatrix_isometry (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    (rankSectorMatrix mu hmu k)ᴴ*rankSectorMatrix mu hmu k=1 := by
  ext a b
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,rankSectorMatrix_apply,
    ← starRingEnd_apply,inner_conj_symm]
  rw [(partitionBasis _ _).sum_inner_mul_inner,(rankSectorEmbedding mu hmu k).inner_map_map]
  exact orthonormal_iff_ite.mp (partitionBasis mu hmu).orthonormal a b

def coordinateTensorMatrix (n r k : ℕ) : Matrix (Fin n → Fin (r+k)) (Fin n → Fin r) ℂ :=
  LinearMap.toMatrix (registerBasis (Fin n → Fin r)).toOrthonormalBasis.toBasis
    (registerBasis (Fin n → Fin (r+k))).toOrthonormalBasis.toBasis
    (coordinateTensorEmbedding n r k).toLinearMap

def PhysicalHighestTensor.liftEmbeddingMatrix (H : PhysicalHighestTensor n r) (k : ℕ) :
    Matrix (Fin n → Fin (r+k)) (PartitionIndex (padPartition H.weight k) (padPartition_antitone _ H.weight_antitone k)) ℂ :=
  (H.coordinateLift k).embeddingMatrix

/-- Exact canonical rank restriction inside every induced physical copy. -/
theorem PhysicalHighestTensor.coordinateLift_embeddingMatrix (H : PhysicalHighestTensor n r) (k : ℕ) :
    H.liftEmbeddingMatrix k*rankSectorMatrix H.weight H.weight_antitone k =
      coordinateTensorMatrix n r k*H.embeddingMatrix := by
  change LinearMap.toMatrix
      (partitionBasis (padPartition H.weight k) (padPartition_antitone _ H.weight_antitone k)).toBasis
      (registerBasis (Fin n → Fin (r+k))).toOrthonormalBasis.toBasis
      (H.coordinateLift k).canonicalEmbedding.toLinearMap *
    LinearMap.toMatrix (partitionBasis H.weight H.weight_antitone).toBasis
      (partitionBasis (padPartition H.weight k) (padPartition_antitone _ H.weight_antitone k)).toBasis
      (rankSectorEmbedding H.weight H.weight_antitone k).toLinearMap = _
  unfold coordinateTensorMatrix PhysicalHighestTensor.embeddingMatrix
  rw [← LinearMap.toMatrix_comp,← LinearMap.toMatrix_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact H.coordinateLift_canonicalEmbedding k x

end Cloning.TensorLie
