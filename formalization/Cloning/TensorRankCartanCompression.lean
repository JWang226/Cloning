import Cloning.TensorRankCartanRestriction
import Cloning.MatrixRankCompressionFidelity

/-! Exact compression of the actual physical Cartan channel for every matrix,
including arbitrary positive and non-flat input and target states. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
namespace Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {r : ℕ}

def rankCartanRatio (mu nu : Fin r→ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) : ℝ :=
  ((partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k):ℝ)/
    (partitionDimension mu hmu:ℝ)) /
  ((partitionDimension (fun a=>padPartition mu k a+padPartition nu k a)
      (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)):ℝ)/
    (partitionDimension (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu):ℝ))

/-- Identification with the manuscript's crossing-root product `R_mu/R_(mu+nu)`. -/
theorem rankCartanRatio_eq_dimensionRatio (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    rankCartanRatio mu nu hmu hnu k =
      Cloning.YoungDimensionRatio.dimensionRatio r k (fun a=>(mu a:ℝ)) /
      Cloning.YoungDimensionRatio.dimensionRatio r k (fun a=>((mu a+nu a:ℕ):ℝ)) := by
  rw [rankCartanRatio,←partitionDimension_pad_ratio mu hmu k,
    ←partitionDimension_pad_ratio (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu) k]
  rw [partitionDimension_congr _ _
    (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)
    (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
    (padPartition_add mu nu k)]

/-- Compression onto the exact smaller-rank output support, for every complex
input operator, has precisely the physical dimension-ratio coefficient. -/
theorem physicalCartanMatrixChannel_rank_compression (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    let Ja := rankSectorEmbeddingMatrix mu hmu k
    let Jc := rankSumSectorEmbeddingMatrix mu nu hmu hnu k
    Jcᴴ*((physicalCartanMatrixChannel (padPartition mu k) (padPartition nu k)
        (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toFun (Ja*X*Jaᴴ))*Jc =
      rankCartanRatio mu nu hmu hnu k • (physicalCartanMatrixChannel mu nu hmu hnu).toFun X := by
  simp only [physicalCartanMatrixChannel_apply]
  exact Cloning.Compression.sectorMap_compression _ _ _ _ _ X _ _ _ _
    (rankSectorEmbeddingMatrix_isometry mu hmu k) (rankSectorEmbeddingMatrix_isometry nu hnu k)
    (rankCartanMatrix_restriction mu nu hmu hnu k)
    (Nat.cast_ne_zero.mpr (partitionDimension_pos _ _).ne')
    (Nat.cast_ne_zero.mpr (partitionDimension_pos _ _).ne')
    (Nat.cast_ne_zero.mpr (partitionDimension_pos _ _).ne')

/-- Equation `channel-compression` for the constructed physical rank embeddings
and actual CPTP Cartan channels; no representation square is assumed. -/
theorem physicalCartanMatrixChannel_rank_supported_compression (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) :
    let Ja := rankSectorEmbeddingMatrix mu hmu k
    let Jc := rankSumSectorEmbeddingMatrix mu nu hmu hnu k
    (Jc*Jcᴴ)*((physicalCartanMatrixChannel (padPartition mu k) (padPartition nu k)
        (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toFun (Ja*X*Jaᴴ))*(Jc*Jcᴴ) =
      rankCartanRatio mu nu hmu hnu k •
        (Jc*(physicalCartanMatrixChannel mu nu hmu hnu).toFun X*Jcᴴ) := by
  dsimp only
  calc
    _ = rankSumSectorEmbeddingMatrix mu nu hmu hnu k *
        ((rankSumSectorEmbeddingMatrix mu nu hmu hnu k)ᴴ *
          ((physicalCartanMatrixChannel (padPartition mu k) (padPartition nu k)
            (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toFun
            (rankSectorEmbeddingMatrix mu hmu k*X*(rankSectorEmbeddingMatrix mu hmu k)ᴴ)) *
          rankSumSectorEmbeddingMatrix mu nu hmu hnu k) *
        (rankSumSectorEmbeddingMatrix mu nu hmu hnu k)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [physicalCartanMatrixChannel_rank_compression]
      simp only [Matrix.mul_smul,Matrix.smul_mul]

/-- Exact physical root-fidelity factorization for every positive smaller-rank
input and target, hence in particular for every positive supported spectrum. -/
theorem physicalCartanMatrixChannel_rank_fidelity (mu nu : Fin r→ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ)
    (X : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (Y : Matrix (PartitionIndex (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu)) _ ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    let Ja := rankSectorEmbeddingMatrix mu hmu k
    let Jc := rankSumSectorEmbeddingMatrix mu nu hmu hnu k
    Cloning.MatrixFidelity.fidelity
      ((physicalCartanMatrixChannel (padPartition mu k) (padPartition nu k)
        (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toFun (Ja*X*Jaᴴ))
      (Jc*Y*Jcᴴ) = Real.sqrt (rankCartanRatio mu nu hmu hnu k) *
        Cloning.MatrixFidelity.fidelity ((physicalCartanMatrixChannel mu nu hmu hnu).toFun X) Y := by
  simp only [physicalCartanMatrixChannel_apply]
  exact Cloning.Compression.sectorMap_fidelity_factorization _ _ _ _ _ X Y _ _ _ _
    (rankSectorEmbeddingMatrix_isometry mu hmu k) (rankSectorEmbeddingMatrix_isometry nu hnu k)
    (rankSumSectorEmbeddingMatrix_isometry mu nu hmu hnu k)
    (rankCartanMatrix_restriction mu nu hmu hnu k)
    (Nat.cast_pos.mpr (partitionDimension_pos _ _))
    (Nat.cast_pos.mpr (partitionDimension_pos _ _))
    (Nat.cast_pos.mpr (partitionDimension_pos _ _))
    (Nat.cast_pos.mpr (partitionDimension_pos _ _)) hX hY

end Cloning.TensorLie
