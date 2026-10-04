import Cloning.TensorPositiveSpectrumCompression
import Cloning.TensorRankCartanRestriction
import Cloning.TensorFlatProjectorGibbsState

/-! Matrix coordinates and exact support compression of arbitrary sector Gibbs
states, including the transported sum partition used by the physical Cartan map. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionGibbsMatrix (mu : Fin d → ℕ) (hmu : Antitone mu) (p : Fin d → ℝ) :=
  matrixOf (partitionBasis mu hmu)
    (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p).1

theorem partitionGibbsMatrix_posSemidef (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p : Fin d → ℝ) (hp : ∀a,0≤p a) : (partitionGibbsMatrix mu hmu p).PosSemidef :=
  matrixOf_posSemidef _ (sectorGibbsDensity_nonneg_of_nonneg _ _ _ _ p hp)

theorem partitionMatrixState_partitionGibbsMatrix (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p : Fin d → ℝ) (hp : ∀a,0≤p a) :
    partitionMatrixState mu hmu (partitionGibbsMatrix mu hmu p)
      (partitionGibbsMatrix_posSemidef mu hmu p hp) = nonnegativePartitionGibbsPositive mu hmu p hp := by
  apply Subtype.ext
  apply Subtype.ext
  exact basis_ofMatrix_matrixOf _ _

section Basis
variable {H K I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem basis_matrixOf_eq_toMatrix (b : OrthonormalBasis I ℂ H) (A : H →L[ℂ] H) :
    matrixOf b A=LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap := by
  ext i j
  simp [matrixOf,LinearMap.toMatrix_apply,OrthonormalBasis.repr_apply_apply]

theorem basis_matrixOf_conjugation (bH : OrthonormalBasis I ℂ H)
    (bK : OrthonormalBasis J ℂ K) (V : H →L[ℂ] K) (A : H →L[ℂ] H) :
    let W := LinearMap.toMatrix bH.toBasis bK.toBasis V.toLinearMap
    matrixOf bK (V.comp (A.comp V.adjoint))=W*matrixOf bH A*Wᴴ := by
  dsimp only
  have ha : LinearMap.toMatrix bK.toBasis bH.toBasis V.adjoint.toLinearMap=
      (LinearMap.toMatrix bH.toBasis bK.toBasis V.toLinearMap)ᴴ := by
    ext i j
    simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply,
      Matrix.conjTranspose_apply,← starRingEnd_apply,inner_conj_symm]
    exact ContinuousLinearMap.adjoint_inner_right V (bH i) (bK j)
  rw [basis_matrixOf_eq_toMatrix,basis_matrixOf_eq_toMatrix]
  change LinearMap.toMatrix bK.toBasis bK.toBasis
    (V.toLinearMap.comp (A.toLinearMap.comp V.adjoint.toLinearMap))=_
  rw [LinearMap.toMatrix_comp bK.toBasis bH.toBasis bK.toBasis,
    LinearMap.toMatrix_comp bK.toBasis bH.toBasis bH.toBasis,ha,Matrix.mul_assoc]

end Basis

/-- The exact conditional-support identity in physical partition bases. -/
theorem partitionGibbsMatrix_padSpectrum (mu : Fin r → ℕ) (hmu : Antitone mu)
    (k : ℕ) (p : Fin r → ℝ) (hp : ∀a,0≤p a) :
    partitionGibbsMatrix (padPartition mu k) (padPartition_antitone mu hmu k) (padSpectrum p k)=
      rankSectorEmbeddingMatrix mu hmu k * partitionGibbsMatrix mu hmu p *
        (rankSectorEmbeddingMatrix mu hmu k)ᴴ := by
  unfold partitionGibbsMatrix
  rw [sectorGibbsDensity_padSpectrum mu hmu k p hp]
  exact basis_matrixOf_conjugation (partitionBasis mu hmu)
    (partitionBasis (padPartition mu k) (padPartition_antitone mu hmu k))
    (rankSectorEmbedding mu hmu k).toContinuousLinearMap
    (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p).1

private theorem partitionGibbsMatrix_padSpectrum_congr
    (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) (eta : Fin (r+k) → ℕ)
    (heta : Antitone eta) (he : padPartition mu k=eta)
    (p : Fin r → ℝ) (hp : ∀a,0≤p a) :
    let J := (partitionSectorCongr _ _ (padPartition_antitone mu hmu k) heta he).toLinearIsometry.comp
      (rankSectorEmbedding mu hmu k)
    let M := LinearMap.toMatrix (partitionBasis mu hmu).toBasis (partitionBasis eta heta).toBasis J.toLinearMap
    partitionGibbsMatrix eta heta (padSpectrum p k)=M*partitionGibbsMatrix mu hmu p*Mᴴ := by
  subst eta
  exact partitionGibbsMatrix_padSpectrum mu hmu k p hp

/-- The output-sector version uses exactly the sum-embedding matrix in the
proved rank-restriction square for the Cartan inclusion. -/
theorem partitionGibbsMatrix_padSpectrum_sum (mu nu : Fin r → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ)
    (p : Fin r → ℝ) (hp : ∀a,0≤p a) :
    partitionGibbsMatrix (fun a => padPartition mu k a+padPartition nu k a)
      (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
      (padSpectrum p k) =
      rankSumSectorEmbeddingMatrix mu nu hmu hnu k *
        partitionGibbsMatrix (fun a => mu a+nu a) (sumPartition_antitone mu nu hmu hnu) p *
          (rankSumSectorEmbeddingMatrix mu nu hmu hnu k)ᴴ :=
  partitionGibbsMatrix_padSpectrum_congr _ (sumPartition_antitone mu nu hmu hnu) k _
    (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
    (padPartition_add mu nu k) p hp

end Cloning.TensorLie
