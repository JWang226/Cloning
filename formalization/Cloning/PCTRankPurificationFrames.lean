import Cloning.PCTRankPurificationVectorization
import Cloning.PCTRankPurificationCoefficients
import Cloning.PCTRankPurificationBlockMatrices

/-! Complete physical frames compare the normalized ambient moment with
its literal smaller-environment Haar moment. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.TensorLie Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {n r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

def physicalFrame (L : List (PhysicalHighestTensor n r)) :
    Matrix (Fin n → Fin r) (PhysicalSchurBasisIndex L) ℂ :=
  fun w a => (L.get a.1).embeddingMatrix w a.2

theorem physicalFrame_complete (L : List (PhysicalHighestTensor n r))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆i : Fin L.length,(L.get i).sector)=⊤) :
    physicalFrame L*(physicalFrame L)ᴴ=1 := by
  rw [← sum_embeddingMatrix_projection L hL hspan]
  ext w v
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,physicalFrame,PhysicalSchurBasisIndex,
    Fintype.sum_sigma,Matrix.sum_apply]

@[simp] theorem physicalFrame_block (L : List (PhysicalHighestTensor n r))
    (X : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)
    (i j : Fin L.length) (a : PartitionIndex (L.get i).weight (L.get i).weight_antitone)
    (b : PartitionIndex (L.get j).weight (L.get j).weight_antitone) :
    ((physicalFrame L)ᴴ*X*physicalFrame L) ⟨i,a⟩ ⟨j,b⟩=
      ((L.get i).embeddingMatrixᴴ*X*(L.get j).embeddingMatrix) a b := rfl

def normalizedCoordinateAction (k : ℕ)
    (N : Matrix (Fin n → Fin (r+k)) (Fin n → Fin (r+k)) ℂ)
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ :=
  (coordinateTensorMatrix n r k)ᴴ*N*tensorPower n U*coordinateTensorMatrix n r k

theorem normalizedCoordinateAction_block (H J : PhysicalHighestTensor n r) (k : ℕ)
    (N : Matrix (Fin n → Fin (r+k)) (Fin n → Fin (r+k)) ℂ) (hN : Nᴴ=N)
    (α : ℝ) (hNE : N*H.liftEmbeddingMatrix k=(α : ℂ) • H.liftEmbeddingMatrix k)
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) :
    H.embeddingMatrixᴴ*normalizedCoordinateAction k N U*J.embeddingMatrix=
      (α : ℂ) • ((rankSectorMatrix H.weight H.weight_antitone k)ᴴ*
        ((H.liftEmbeddingMatrix k)ᴴ*J.liftEmbeddingMatrix k)*
        partitionActionMatrix (padPartition J.weight k) (padPartition_antitone _ J.weight_antitone k) U*
        rankSectorMatrix J.weight J.weight_antitone k) := by
  have hEN : (H.liftEmbeddingMatrix k)ᴴ*N=(α : ℂ) • (H.liftEmbeddingMatrix k)ᴴ := by
    have hh := congrArg Matrix.conjTranspose hNE
    simpa only [Matrix.conjTranspose_mul,hN,Matrix.conjTranspose_smul,
      Complex.star_def,Complex.conj_ofReal] using hh
  have hT : tensorPower n U*J.liftEmbeddingMatrix k=J.liftEmbeddingMatrix k*
      partitionActionMatrix (padPartition J.weight k) (padPartition_antitone _ J.weight_antitone k) U :=
    (J.coordinateLift k).embeddingMatrix_intertwines U
  calc
    _ = ((coordinateTensorMatrix n r k*H.embeddingMatrix)ᴴ*N)*
        (tensorPower n U*(coordinateTensorMatrix n r k*J.embeddingMatrix)) := by
      simp only [normalizedCoordinateAction,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = (((H.liftEmbeddingMatrix k*rankSectorMatrix H.weight H.weight_antitone k)ᴴ)*N)*
        (tensorPower n U*(J.liftEmbeddingMatrix k*rankSectorMatrix J.weight J.weight_antitone k)) := by
      rw [H.coordinateLift_embeddingMatrix,J.coordinateLift_embeddingMatrix]
    _ = _ := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (H.liftEmbeddingMatrix k)ᴴ,hEN,
        ← Matrix.mul_assoc (tensorPower n U),hT]
      simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]

theorem tensorPower_block_diagonal (H : PhysicalHighestTensor n r) (V : Matrix (Fin r) (Fin r) ℂ) :
    H.embeddingMatrixᴴ*tensorPower n V*H.embeddingMatrix=partitionActionMatrix H.weight H.weight_antitone V := by
  rw [Matrix.mul_assoc,H.embeddingMatrix_intertwines,← Matrix.mul_assoc,H.embeddingMatrix_isometry,Matrix.one_mul]

theorem tensorPower_block_orthogonal (H J : PhysicalHighestTensor n r)
    (hHJ : H.embeddingMatrixᴴ*J.embeddingMatrix=0) (V : Matrix (Fin r) (Fin r) ℂ) :
    H.embeddingMatrixᴴ*tensorPower n V*J.embeddingMatrix=0 := by
  rw [Matrix.mul_assoc,J.embeddingMatrix_intertwines,← Matrix.mul_assoc,hHJ,Matrix.zero_mul]

theorem normalizedCoordinateAction_block_diagonal (H : PhysicalHighestTensor n r) (k : ℕ)
    (N : Matrix (Fin n → Fin (r+k)) (Fin n → Fin (r+k)) ℂ) (hN : Nᴴ=N)
    (α : ℝ) (hNE : N*H.liftEmbeddingMatrix k=(α : ℂ) • H.liftEmbeddingMatrix k)
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    H.embeddingMatrixᴴ*normalizedCoordinateAction k N U*H.embeddingMatrix=
      (α : ℂ) • compressedPartitionAction (padPartition H.weight k)
        (padPartition_antitone _ H.weight_antitone k) (rankSectorMatrix H.weight H.weight_antitone k) U := by
  have he : (H.liftEmbeddingMatrix k)ᴴ*H.liftEmbeddingMatrix k=1 :=
    (H.coordinateLift k).embeddingMatrix_isometry
  rw [normalizedCoordinateAction_block H H k N hN α hNE,he,Matrix.mul_one]
  rfl

theorem normalizedCoordinateAction_block_orthogonal (H J : PhysicalHighestTensor n r) (k : ℕ)
    (N : Matrix (Fin n → Fin (r+k)) (Fin n → Fin (r+k)) ℂ) (hN : Nᴴ=N)
    (α : ℝ) (hNE : N*H.liftEmbeddingMatrix k=(α : ℂ) • H.liftEmbeddingMatrix k)
    (hHJ : (H.liftEmbeddingMatrix k)ᴴ*J.liftEmbeddingMatrix k=0)
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) :
    H.embeddingMatrixᴴ*normalizedCoordinateAction k N U*J.embeddingMatrix=0 := by
  rw [normalizedCoordinateAction_block H J k N hN α hNE,hHJ,Matrix.mul_zero,
    Matrix.zero_mul,Matrix.zero_mul,smul_zero]

end Cloning.PCTRankPurification
