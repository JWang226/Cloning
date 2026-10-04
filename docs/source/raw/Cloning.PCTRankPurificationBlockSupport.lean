import Cloning.PCTRankPurificationBlockHaar

/-! The actual Haar support contains the full coordinate tensor input.
Consequently the completed purifier has the exact square-root action on
all supported complex matrices, without a support premise. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix Kronecker MatrixOrder ComplexOrder
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.TensorLie Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
variable {n r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable (L : List (PhysicalHighestTensor n r))
  (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
    (fun i => (L.get i).sector.subtypeₗᵢ))
  (hspan : (⨆ i : Fin L.length,(L.get i).sector)=⊤)
include hL hspan

theorem coordinateHaarSupport_mul_liftEmbedding (k : ℕ) (j : Fin L.length) :
    momentSupport (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
      (L.get j).liftEmbeddingMatrix k=(L.get j).liftEmbeddingMatrix k := by
  apply momentSupport_mul_isometry (coordinateHaarMarginal n r k)
    (coordinateHaarMarginal_posSemidef n r k) ((L.get j).liftEmbeddingMatrix k)
    (((L.get j).coordinateLift k).embeddingMatrix_isometry)
    ((partitionDimension (L.get j).weight (L.get j).weight_antitone : ℝ)/
      (partitionDimension (padPartition (L.get j).weight k)
        (padPartition_antitone _ (L.get j).weight_antitone k) : ℝ))
    (div_pos (Nat.cast_pos.mpr (partitionDimension_pos _ _)) (Nat.cast_pos.mpr (partitionDimension_pos _ _)))
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast] using
    coordinateHaarMarginal_mul_liftEmbedding L hL hspan k j

theorem coordinateHaarSupport_mul_coordinateTensor (k : ℕ) :
    momentSupport (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
      coordinateTensorMatrix n r k=coordinateTensorMatrix n r k := by
  rw [coordinateTensorMatrix_eq_sum_lift L hL hspan k,Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,coordinateHaarSupport_mul_liftEmbedding L hL hspan]

/-- The normalizer's complete action on the actual coordinate tensor input. -/
theorem coordinateHaarNormalizer_mul_coordinateTensor (k : ℕ) :
    momentNormalizer (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
      coordinateTensorMatrix n r k=
      ∑ i : Fin L.length,(rankMomentScale (L.get i).weight (L.get i).weight_antitone k : ℂ) •
        (((L.get i).liftEmbeddingMatrix k*rankSectorMatrix (L.get i).weight (L.get i).weight_antitone k)*
          (L.get i).embeddingMatrixᴴ) := by
  rw [coordinateTensorMatrix_eq_sum_lift L hL hspan k,Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,coordinateHaarNormalizer_mul_liftEmbedding L hL hspan]
  simp only [Matrix.smul_mul]

/-- The actual physical coordinate tensor input is contained in the derived
Haar support; the channel completion contributes exactly zero. -/
theorem rankPurificationChannel_apply_coordinate_supported (k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (X : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (coordinateTensorMatrix n r k*X*(coordinateTensorMatrix n r k)ᴴ)=
      purificationMap
        (normalizedMoment (rectangularHaarMoment n (coordinateInclusionMatrix r k))
          (partialTrace_rectangularHaarMoment_posSemidef n (coordinateInclusionMatrix r k)))
        (coordinateTensorMatrix n r k*X*(coordinateTensorMatrix n r k)ᴴ) := by
  apply supportedPurificationChannel_apply_supported
  change momentSupport (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
    (coordinateTensorMatrix n r k*X*(coordinateTensorMatrix n r k)ᴴ)=_
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,coordinateHaarSupport_mul_coordinateTensor L hL hspan]

end Cloning.PCTRankPurification
