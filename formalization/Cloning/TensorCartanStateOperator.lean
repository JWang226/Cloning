import Cloning.TensorCartanStateCutoff

/-! Basis-free operator action of the constructed physical Cartan channel. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
open Cloning.PCTPurificationChannel
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

section Basis
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem basis_projection_eq_one (b : OrthonormalBasis I ℂ H) : projection b = 1 := by
  ext x
  rw [projection_apply]
  simpa only [OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.one_apply] using b.sum_repr x

theorem basis_ofMatrix_matrixOf (b : OrthonormalBasis I ℂ H) (A : H →L[ℂ] H) :
    ofMatrix b (matrixOf b A) = A := by
  rw [ofMatrix_matrixOf, basis_projection_eq_one, one_mul, mul_one]

theorem basis_toMatrix_ofMatrix (b : OrthonormalBasis I ℂ H) (M : Matrix I I ℂ) :
    LinearMap.toMatrix b.toBasis b.toBasis (ofMatrix b M).toLinearMap = M := by
  ext i j
  simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    matrixOf] using congrArg (fun X => X i j) (matrixOf_ofMatrix b.orthonormal M)

theorem basis_ofMatrix_smul (b : OrthonormalBasis I ℂ H) (c : ℂ) (M : Matrix I I ℂ) :
    ofMatrix b (c • M) = c • ofMatrix b M := by
  simp [ofMatrix_eq_sum, Matrix.smul_apply, Finset.smul_sum, smul_smul]

theorem basis_ofMatrix_compression (bH : OrthonormalBasis I ℂ H)
    (bK : OrthonormalBasis J ℂ K) (V : H →L[ℂ] K) (M : Matrix J J ℂ) :
    let W := LinearMap.toMatrix bH.toBasis bK.toBasis V.toLinearMap
    ofMatrix bH (Wᴴ * M * W) = V.adjoint.comp ((ofMatrix bK M).comp V) := by
  intro W
  have ha : LinearMap.toMatrix bK.toBasis bH.toBasis V.adjoint.toLinearMap = Wᴴ := by
    ext i j
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_inner_right,
      W, Matrix.conjTranspose_apply]
    exact (inner_conj_symm _ _).symm
  suffices he : (ofMatrix bH (Wᴴ * M * W)).toLinearMap =
      (V.adjoint.comp ((ofMatrix bK M).comp V)).toLinearMap by
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) he
  apply (LinearMap.toMatrix bH.toBasis bH.toBasis).injective
  rw [basis_toMatrix_ofMatrix]
  change Wᴴ * M * W = LinearMap.toMatrix bH.toBasis bH.toBasis
    (V.adjoint.toLinearMap.comp ((ofMatrix bK M).toLinearMap.comp V.toLinearMap))
  rw [LinearMap.toMatrix_comp bH.toBasis bK.toBasis bH.toBasis,
    LinearMap.toMatrix_comp bH.toBasis bK.toBasis bK.toBasis,
    ha, basis_toMatrix_ofMatrix, ← Matrix.mul_assoc]

end Basis

variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem partitionRegisterEquiv_symm_basis (mu : Fin d → ℕ) (hmu : Antitone mu)
    (i : PartitionIndex mu hmu) :
    (partitionRegisterEquiv mu hmu).symm (registerBasis _ i) = partitionBasis mu hmu i := by
  change (partitionBasis mu hmu).repr.symm
    ((registerBasis _).toOrthonormalBasis.repr (registerBasis _ i)) = _
  rw [← HilbertBasis.coe_toOrthonormalBasis]
  rw [OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]

theorem partitionMatrixOperator_eq_matrixLift (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    partitionMatrixOperator mu hmu M = matrixLift (partitionBasis mu hmu) M := by
  change conjugationLinearMap (partitionRegisterEquiv mu hmu).symm.toLinearIsometry.toContinuousLinearMap
    (matrixLift (registerBasis _) M) = _
  simp only [matrixLift, map_sum, map_smul, conjugationLinearMap_rankOneOperator,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    partitionRegisterEquiv_symm_basis]

theorem partitionMatrixOperator_matrixOf (mu : Fin d → ℕ) (hmu : Antitone mu)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    partitionMatrixOperator mu hmu (matrixOf (partitionBasis mu hmu) A.1) = A := by
  rw [partitionMatrixOperator_eq_matrixLift]
  apply Subtype.ext
  exact basis_ofMatrix_matrixOf _ _

def cartanProductOperator (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (A : cyclicSector (partitionHighestTensor mu hmu) →L[ℂ]
      cyclicSector (partitionHighestTensor mu hmu)) :=
  ofMatrix (cartanProductBasis mu nu hmu hnu)
    (matrixOf (partitionBasis mu hmu) A ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ))

/-- The already constructed all-input CPTP channel has the literal
dimension-ratio times adjoint-compression formula on arbitrary trace-class inputs. -/
theorem physicalCartanChannel_operator
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (A : TraceClass (cyclicSector (partitionHighestTensor mu hmu))) :
    ((physicalCartanChannel mu nu hmu hnu).toLinearMap A).1 =
      (((partitionDimension mu hmu : ℝ) /
        (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ) •
      (cartanInclusion mu nu hmu hnu).toContinuousLinearMap.adjoint.comp
        ((cartanProductOperator mu nu hmu hnu A.1).comp
          (cartanInclusion mu nu hmu hnu).toContinuousLinearMap) := by
  let M := matrixOf (partitionBasis mu hmu) A.1
  have hA : partitionMatrixOperator mu hmu M = A := partitionMatrixOperator_matrixOf _ _ A
  have hc := congrArg Subtype.val
    (physicalCartanChannel_partitionMatrixOperator mu nu hmu hnu M)
  rw [hA, partitionMatrixOperator_eq_matrixLift] at hc
  change ((physicalCartanChannel mu nu hmu hnu).toLinearMap A).1 =
    ofMatrix (partitionBasis _ (sumPartition_antitone mu nu hmu hnu))
      (Cloning.Compression.sectorMap _ _ (cartanMatrix mu nu hmu hnu) M) at hc
  have hcomp := basis_ofMatrix_compression
    (partitionBasis _ (sumPartition_antitone mu nu hmu hnu))
    (cartanProductBasis mu nu hmu hnu)
    (cartanInclusion mu nu hmu hnu).toContinuousLinearMap
    (M ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ))
  have hs := basis_ofMatrix_smul
    (partitionBasis _ (sumPartition_antitone mu nu hmu hnu))
    ((((partitionDimension mu hmu : ℝ) /
      (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ))
    ((cartanMatrix mu nu hmu hnu)ᴴ * (M ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ)) *
      cartanMatrix mu nu hmu hnu)
  have hfinal := hs.trans (congrArg (fun
    (T : cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu)) →L[ℂ]
      cyclicSector (partitionHighestTensor _ (sumPartition_antitone mu nu hmu hnu))) =>
    ((((partitionDimension mu hmu : ℝ) /
      (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ)) • T) hcomp)
  have hr : Cloning.Compression.sectorMap (partitionDimension mu hmu : ℝ)
      (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)
      (cartanMatrix mu nu hmu hnu) M =
      ((((partitionDimension mu hmu : ℝ) /
        (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ)) : ℂ)) •
      ((cartanMatrix mu nu hmu hnu)ᴴ * (M ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ)) *
        cartanMatrix mu nu hmu hnu) := by
    simpa only [Cloning.Compression.sectorMap, Complex.ofReal_div, RCLike.ofReal_div] using
      RCLike.real_smul_eq_coe_smul (K := ℂ)
      ((partitionDimension mu hmu : ℝ) /
        (partitionDimension _ (sumPartition_antitone mu nu hmu hnu) : ℝ))
      ((cartanMatrix mu nu hmu hnu)ᴴ * (M ⊗ₖ (1 : Matrix (PartitionIndex nu hnu) _ ℂ)) *
        cartanMatrix mu nu hmu hnu)
  exact hc.trans ((congrArg (ofMatrix (partitionBasis _
    (sumPartition_antitone mu nu hmu hnu))) hr).trans hfinal)

end Cloning.TensorLie
