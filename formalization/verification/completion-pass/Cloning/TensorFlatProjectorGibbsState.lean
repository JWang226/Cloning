import Cloning.TensorFlatProjectorGibbs
import Cloning.TensorCloningTransitionCovariance

/-! Exact flat-state fidelity for the actual compatible physical transition channel. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
open Cloning.TensorCloning Cloning.YoungDimensionRatio
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def nonnegativePartitionGibbsPositive (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    PositiveTraceClass (cyclicSector (partitionHighestTensor mu hmu)) :=
  ⟨sectorGibbsDensity _ mu (partitionHighestTensor_cartan mu hmu)
    (partitionHighestTensor_raising_zero mu hmu) p,
    sectorGibbsDensity_nonneg_of_nonneg _ _ _ _ p hp⟩

/-- The general physical Gibbs normalization specializes to the constructed
rank-flat support state at every padded partition. -/
theorem nonnegativePartitionGibbsPositive_pad_rankFlat (mu : Fin r → ℕ) (hmu : Antitone mu)
    (k : ℕ) (hr : 0 < r) :
    nonnegativePartitionGibbsPositive (padPartition mu k) (padPartition_antitone mu hmu k)
      (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) = rankFlatSectorState mu hmu k := by
  let eta := padPartition mu k
  let heta : Antitone eta := padPartition_antitone mu hmu k
  let Z := physicalSectorCharacter eta (rankFlatSpectrum r k)
  have hZ : 0 < Z := by
    dsimp [Z,eta]
    rw [physicalSectorCharacter_rankFlat mu hmu k]
    exact div_pos (Nat.cast_pos.mpr (partitionDimension_pos mu hmu)) (pow_pos (Nat.cast_pos.mpr hr) _)
  have he := congrArg (ofMatrix (partitionBasis eta heta)) (partitionActionMatrix_rankFlat mu hmu k)
  have hm : partitionActionMatrix eta heta (Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ))) =
      matrixOf (partitionBasis eta heta) (sectorGibbsOperator (partitionHighestTensor eta heta) eta
        (partitionHighestTensor_cartan eta heta) (partitionHighestTensor_raising_zero eta heta)
        (rankFlatSpectrum r k)) := by
    ext i j
    exact partitionActionMatrix_apply _ _ _ i j
  rw [hm, basis_ofMatrix_matrixOf] at he
  change sectorGibbsOperator (partitionHighestTensor eta heta) eta (partitionHighestTensor_cartan eta heta) (partitionHighestTensor_raising_zero eta heta) (rankFlatSpectrum r k) =
    ofMatrix (partitionBasis eta heta) ((Z : ℂ) • rankFlatSectorDensity mu hmu k) at he
  rw [basis_ofMatrix_smul] at he
  have hz : sectorPartitionFunction (partitionHighestTensor eta heta) eta
      (partitionHighestTensor_cartan eta heta) (partitionHighestTensor_raising_zero eta heta)
      (rankFlatSpectrum r k) = Z := by
    simp only [Z, physicalSectorCharacter, dif_pos heta]
  apply Subtype.ext
  apply Subtype.ext
  change (((sectorPartitionFunction (partitionHighestTensor eta heta) eta (partitionHighestTensor_cartan eta heta) (partitionHighestTensor_raising_zero eta heta) (rankFlatSpectrum r k))⁻¹ : ℝ) : ℂ) •
    sectorGibbsOperator (partitionHighestTensor eta heta) eta (partitionHighestTensor_cartan eta heta) (partitionHighestTensor_raising_zero eta heta) (rankFlatSpectrum r k) = ofMatrix (partitionBasis eta heta) (rankFlatSectorDensity mu hmu k)
  rw [hz, he]
  have hc : ((Z⁻¹ : ℝ) : ℂ) * (Z : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hZ.ne', Complex.ofReal_one]
  convert congrArg (fun c : ℂ => c • ofMatrix (partitionBasis eta heta)
      (rankFlatSectorDensity mu hmu k)) hc using 1 <;> simp only [smul_smul, one_smul]


end Cloning.TensorLie
