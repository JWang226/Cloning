import Cloning.TensorCartanFrame
import Cloning.TensorCartanIntertwiner
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Actual finite coordinates of the physical Cartan isometry and its Lie
intertwining. Dimensions are the actual cyclic-sector dimensions. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionDimension (mu : Fin d → ℕ) (hmu : Antitone mu) : ℕ :=
  Module.finrank ℂ (cyclicSector (partitionHighestTensor mu hmu))

abbrev PartitionIndex (mu : Fin d → ℕ) (hmu : Antitone mu) := Fin (partitionDimension mu hmu)

def partitionBasis (mu : Fin d → ℕ) (hmu : Antitone mu) :
    OrthonormalBasis (PartitionIndex mu hmu) ℂ (cyclicSector (partitionHighestTensor mu hmu)) :=
  stdOrthonormalBasis ℂ _

theorem partitionDimension_pos (mu : Fin d → ℕ) (hmu : Antitone mu) :
    0 < partitionDimension mu hmu := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨partitionHighestTensor mu hmu, highest_mem_cyclicSector _⟩, ?_⟩
  intro he
  have hh := congrArg (fun x : cyclicSector (partitionHighestTensor mu hmu) => ‖x‖) he
  change ‖partitionHighestTensor mu hmu‖ = ‖(0 : TensorRegister (∑ i, mu i) (Fin d))‖ at hh
  rw [partitionHighestTensor_norm, norm_zero] at hh
  norm_num at hh

def partitionGeneratorMatrix (mu : Fin d → ℕ) (hmu : Antitone mu) (a b : Fin d) :
    Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ :=
  LinearMap.toMatrix (partitionBasis mu hmu).toBasis (partitionBasis mu hmu).toBasis
    (partitionGenerator mu hmu a b).toLinearMap

@[simp] theorem partitionGeneratorMatrix_apply
    (mu : Fin d → ℕ) (hmu : Antitone mu) (a b : Fin d) (i j : PartitionIndex mu hmu) :
    partitionGeneratorMatrix mu hmu a b i j =
      ⟪partitionBasis mu hmu i, partitionGenerator mu hmu a b (partitionBasis mu hmu j)⟫_ℂ := by
  simp [partitionGeneratorMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

def cartanProductBasis (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    OrthonormalBasis (PartitionIndex mu hmu × PartitionIndex nu hnu) ℂ
      (tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
        (cyclicSector (partitionHighestTensor nu hnu))) :=
  productSectorBasis _ _ (partitionBasis mu hmu) (partitionBasis nu hnu)

def cartanMatrix (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    Matrix (PartitionIndex mu hmu × PartitionIndex nu hnu)
      (PartitionIndex (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu)) ℂ :=
  LinearMap.toMatrix (partitionBasis _ (sumPartition_antitone mu nu hmu hnu)).toBasis
    (cartanProductBasis mu nu hmu hnu).toBasis (cartanInclusion mu nu hmu hnu).toLinearMap

@[simp] theorem cartanMatrix_apply
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (i : PartitionIndex mu hmu × PartitionIndex nu hnu)
    (j : PartitionIndex (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu)) :
    cartanMatrix mu nu hmu hnu i j =
      ⟪cartanProductBasis mu nu hmu hnu i,
        cartanInclusion mu nu hmu hnu (partitionBasis _ (sumPartition_antitone mu nu hmu hnu) j)⟫_ℂ := by
  simp [cartanMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

/-- The coordinate matrix is actually isometric, because the target frame is
complete on the literal product-sector subspace. -/
theorem cartanMatrix_isometry
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    (cartanMatrix mu nu hmu hnu)ᴴ * cartanMatrix mu nu hmu hnu = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cartanMatrix_apply]
  simp only [← starRingEnd_apply, inner_conj_symm]
  rw [(cartanProductBasis mu nu hmu hnu).sum_inner_mul_inner,
    (cartanInclusion mu nu hmu hnu).inner_map_map]
  exact orthonormal_iff_ite.mp (partitionBasis _ (sumPartition_antitone mu nu hmu hnu)).orthonormal i j

/-- Conjugate-transpose symmetry is inherited from the physical root adjoints. -/
theorem partitionGeneratorMatrix_adjoint
    (mu : Fin d → ℕ) (hmu : Antitone mu) (a b : Fin d) :
    partitionGeneratorMatrix mu hmu b a = (partitionGeneratorMatrix mu hmu a b)ᴴ := by
  ext i j
  simp only [partitionGeneratorMatrix_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, inner_conj_symm]
  have he := cyclicGenerator_adjoint (partitionHighestTensor mu hmu) (fun i => (mu i : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) a b
  change ⟪partitionBasis mu hmu i, cyclicGenerator _ _ _ _ b a (partitionBasis mu hmu j)⟫_ℂ = _
  rw [← he, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- In product coordinates the collective generator is the literal tensor sum. -/
theorem productPartitionGenerator_matrix
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (a b : Fin d) :
    LinearMap.toMatrix (cartanProductBasis mu nu hmu hnu).toBasis
      (cartanProductBasis mu nu hmu hnu).toBasis
      (productPartitionGenerator mu nu hmu hnu a b).toLinearMap =
      partitionGeneratorMatrix mu hmu a b ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ) +
      (1 : Matrix (PartitionIndex mu hmu) _ ℂ) ⊗ₖ partitionGeneratorMatrix nu hnu a b := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    cartanProductBasis, productSectorBasis_apply]
  change ⟪tensorJoin (partitionBasis mu hmu i.1 : TensorRegister (∑ k, mu k) (Fin d))
      (partitionBasis nu hnu i.2 : TensorRegister (∑ k, nu k) (Fin d)),
    collectiveGenerator _ a b
      (tensorJoin (partitionBasis mu hmu j.1 : TensorRegister (∑ k, mu k) (Fin d))
        (partitionBasis nu hnu j.2 : TensorRegister (∑ k, nu k) (Fin d)))⟫_ℂ = _
  rw [collectiveGenerator_tensorJoin, inner_add_right, tensorJoin_inner, tensorJoin_inner]
  change ⟪partitionBasis mu hmu i.1, partitionGenerator mu hmu a b (partitionBasis mu hmu j.1)⟫_ℂ *
      ⟪partitionBasis nu hnu i.2, partitionBasis nu hnu j.2⟫_ℂ +
    ⟪partitionBasis mu hmu i.1, partitionBasis mu hmu j.1⟫_ℂ *
      ⟪partitionBasis nu hnu i.2, partitionGenerator nu hnu a b (partitionBasis nu hnu j.2)⟫_ℂ = _
  simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    partitionGeneratorMatrix_apply, orthonormal_iff_ite.mp (partitionBasis mu hmu).orthonormal,
    orthonormal_iff_ite.mp (partitionBasis nu hnu).orthonormal]

/-- Exact matrix tensor-sum intertwining of the constructed Cartan inclusion. -/
theorem cartanMatrix_intertwines
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (a b : Fin d) :
    (partitionGeneratorMatrix mu hmu a b ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ) +
      (1 : Matrix (PartitionIndex mu hmu) _ ℂ) ⊗ₖ partitionGeneratorMatrix nu hnu a b) *
      cartanMatrix mu nu hmu hnu =
    cartanMatrix mu nu hmu hnu *
      partitionGeneratorMatrix (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu) a b := by
  rw [← productPartitionGenerator_matrix]
  simp only [cartanMatrix, partitionGeneratorMatrix, ← LinearMap.toMatrix_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact (cartanInclusion_intertwines mu nu hmu hnu a b x).symm

end Cloning.TensorLie
