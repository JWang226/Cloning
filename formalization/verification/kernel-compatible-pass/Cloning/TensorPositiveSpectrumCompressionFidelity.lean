import Cloning.TensorRankCartanCompression
import Cloning.TensorPositiveSpectrumCompressionMatrix

/-! The complete exact rank-compression identity for arbitrary supported
spectra: actual Gibbs densities, actual Cartan channels, and actual fidelity.
No flat-spectrum assumption or supplied representation identity remains. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {r d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Root fidelity of the actual Cartan output with the actual normalized
Gibbs target. It is normalized when the partition function is positive;
at zero partition function the density is the zero operator. -/
def nonnegativeCartanGibbsFidelity (mu nu : Fin d→ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d→ℝ) (hp : ∀a,0≤p a) : ℝ :=
  ((nonnegativePartitionGibbsPositive mu hmu p hp).map
    (physicalCartanChannel mu nu hmu hnu).toPositiveTracePreservingMap).rootFidelity
    (nonnegativePartitionGibbsPositive (fun a=>mu a+nu a)
      (sumPartition_antitone mu nu hmu hnu) p hp)

theorem nonnegativeCartanGibbsFidelity_eq_matrix
    (mu nu : Fin d→ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (p : Fin d→ℝ) (hp : ∀a,0≤p a) :
    nonnegativeCartanGibbsFidelity mu nu hmu hnu p hp =
      Cloning.MatrixFidelity.fidelity
        ((physicalCartanMatrixChannel mu nu hmu hnu).toFun (partitionGibbsMatrix mu hmu p))
        (partitionGibbsMatrix (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu) p) := by
  unfold nonnegativeCartanGibbsFidelity
  rw [←partitionMatrixState_partitionGibbsMatrix mu hmu p hp,
    ←partitionMatrixState_partitionGibbsMatrix (fun a=>mu a+nu a)
      (sumPartition_antitone mu nu hmu hnu) p hp,
    physicalCartanChannel_partitionMatrix_fidelity]

/-- Equation `exact-sector-factorization` for arbitrary positive supported
spectra, in fact for every nonnegative spectrum. The coefficient is exactly
the proved Weyl crossing-dimension product `sqrt(R_mu/R_(mu+nu))`. -/
theorem nonnegativeCartanGibbsFidelity_padSpectrum
    (mu nu : Fin r→ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ)
    (p : Fin r→ℝ) (hp : ∀a,0≤p a) :
    nonnegativeCartanGibbsFidelity (padPartition mu k) (padPartition nu k)
      (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)
      (padSpectrum p k) (padSpectrum_nonneg p hp k) =
      Real.sqrt (Cloning.YoungDimensionRatio.dimensionRatio r k (fun a=>(mu a:ℝ)) /
        Cloning.YoungDimensionRatio.dimensionRatio r k (fun a=>((mu a+nu a:ℕ):ℝ))) *
        nonnegativeCartanGibbsFidelity mu nu hmu hnu p hp := by
  rw [nonnegativeCartanGibbsFidelity_eq_matrix,nonnegativeCartanGibbsFidelity_eq_matrix,
    partitionGibbsMatrix_padSpectrum mu hmu k p hp,
    partitionGibbsMatrix_padSpectrum_sum mu nu hmu hnu k p hp,
    physicalCartanMatrixChannel_rank_fidelity mu nu hmu hnu k _ _
      (partitionGibbsMatrix_posSemidef mu hmu p hp)
      (partitionGibbsMatrix_posSemidef _ (sumPartition_antitone mu nu hmu hnu) p hp),
    rankCartanRatio_eq_dimensionRatio]

end Cloning.TensorLie
