import Cloning.TensorFlatProjectorCompression

/-! Exact physical Cartan fidelity for rank-r flat sector states. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
namespace Cloning.TensorLie
open Cloning.MatrixFidelity Cloning.YoungDimensionRatio
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {r k : ℕ}

theorem padPartition_add (mu nu : Fin r → ℕ) (k : ℕ) :
    padPartition (fun a => mu a + nu a) k = fun a => padPartition mu k a + padPartition nu k a := by
  funext a
  induction a using Fin.addCases <;> simp

theorem partitionDimension_congr {d : ℕ} (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (he : mu = nu) :
    partitionDimension mu hmu = partitionDimension nu hnu := by
  subst nu
  rfl

theorem trace_partitionCoordinateProjection_congr (mu nu : Fin (r+k) → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (he : mu = nu) :
    Matrix.trace (partitionCoordinateProjection mu hmu) =
      Matrix.trace (partitionCoordinateProjection nu hnu) := by
  subst nu
  rfl

/-- The normalized support projector is the actual rank-flat sector density. -/
def rankFlatSectorDensity (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :=
  (1/(partitionDimension mu hmu : ℝ)) •
    partitionCoordinateProjection (padPartition mu k) (padPartition_antitone mu hmu k)

theorem rankFlatSectorDensity_posSemidef (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    (rankFlatSectorDensity mu hmu k).PosSemidef :=
  (partitionCoordinateProjection_posSemidef _ _).smul (by positivity)

theorem rankFlatSectorDensity_trace (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    Matrix.trace (rankFlatSectorDensity mu hmu k) = 1 := by
  rw [rankFlatSectorDensity, Matrix.trace_smul, trace_partitionCoordinateProjection_pad]
  change (((1/(partitionDimension mu hmu : ℝ) : ℝ) : ℂ) * (partitionDimension mu hmu : ℂ)) = 1
  push_cast
  exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (partitionDimension_pos mu hmu).ne')

/-- Literal CPTP Cartan-channel fidelity, expressed using actual physical
support and ambient dimensions. -/
theorem physicalCartanMatrixChannel_rankFlat_fidelity_dimensions
    (mu nu : Fin r → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    fidelity
      ((physicalCartanMatrixChannel (padPartition mu k) (padPartition nu k)
        (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toFun
          (rankFlatSectorDensity mu hmu k))
      ((1/(partitionDimension (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu) : ℝ)) •
        partitionCoordinateProjection (fun a => padPartition mu k a + padPartition nu k a)
          (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))) =
      Real.sqrt
        (((partitionDimension (padPartition mu k) (padPartition_antitone mu hmu k) : ℝ) /
          partitionDimension (fun a => padPartition mu k a + padPartition nu k a)
            (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))) *
        ((partitionDimension (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu) : ℝ) /
          partitionDimension mu hmu)) := by
  rw [physicalCartanMatrixChannel_apply, rankFlatSectorDensity]
  apply sectorMap_flat_projector_fidelity
    (V := cartanMatrix (padPartition mu k) (padPartition nu k)
      (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
    (Pa := partitionCoordinateProjection (padPartition mu k) (padPartition_antitone mu hmu k))
    (Pb := partitionCoordinateProjection (padPartition nu k) (padPartition_antitone nu hnu k))
  · exact Nat.cast_pos.mpr (partitionDimension_pos _ _)
  · exact Nat.cast_pos.mpr (partitionDimension_pos _ _)
  · exact Nat.cast_pos.mpr (partitionDimension_pos _ _)
  · exact Nat.cast_pos.mpr (partitionDimension_pos _ _)
  · exact cartanMatrix_isometry _ _ _ _
  · exact partitionCoordinateProjection_idempotent _ _
  · exact partitionCoordinateProjection_idempotent _ _
  · exact partitionCoordinateProjection_posSemidef _ _
  · have ht := trace_partitionCoordinateProjection_pad (k := k)
      (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu)
    have htr := trace_partitionCoordinateProjection_congr _ _
      (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)
      (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
      (padPartition_add mu nu k)
    rw [htr] at ht
    simpa only [Complex.natCast_re] using congrArg Complex.re ht
  · exact cartanMatrix_tensorAction _ _ _ _ (coordinateSupportMatrix r k)

/-- The manuscript's exact crossing-dimension ratio follows from the actual
Weyl dimensions and the actual CPTP Cartan compression. -/
theorem physicalCartanMatrixChannel_rankFlat_fidelity
    (mu nu : Fin r → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    fidelity
      ((physicalCartanMatrixChannel (padPartition mu k) (padPartition nu k)
        (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k)).toFun
          (rankFlatSectorDensity mu hmu k))
      ((1/(partitionDimension (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu) : ℝ)) •
        partitionCoordinateProjection (fun a => padPartition mu k a + padPartition nu k a)
          (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))) =
      Real.sqrt (dimensionRatio r k (fun a => (mu a : ℝ)) /
        dimensionRatio r k (fun a => ((mu a + nu a : ℕ) : ℝ))) := by
  rw [physicalCartanMatrixChannel_rankFlat_fidelity_dimensions mu nu hmu hnu k]
  congr 1
  rw [← partitionDimension_pad_ratio mu hmu k,
    ← partitionDimension_pad_ratio (fun a => mu a + nu a) (sumPartition_antitone mu nu hmu hnu) k]
  rw [partitionDimension_congr _ _
    (padPartition_antitone _ (sumPartition_antitone mu nu hmu hnu) k)
    (sumPartition_antitone _ _ (padPartition_antitone mu hmu k) (padPartition_antitone nu hnu k))
    (padPartition_add mu nu k)]
  field_simp
  <;> ring

end Cloning.TensorLie
