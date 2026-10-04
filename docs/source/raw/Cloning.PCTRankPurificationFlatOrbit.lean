import Cloning.PCTRankPurificationFlatAction
import Cloning.PCTRankPurificationFlatScalar
import Cloning.PCTRankPurificationCovariance

/-! One fixed smaller-environment purifier has the exact embedded Haar
purification action on every physical flat orbit input. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker Matrix.Norms.L2Operator
open Matrix
namespace Cloning.PCTRankPurification
open Cloning.TensorLie Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

theorem coordinate_scalar_tensor_input (n k : ℕ) (c : ℂ) :
    tensorPower n (coordinateInclusionMatrix r k*(c • (1 : Matrix (Fin r) (Fin r) ℂ))*
      (coordinateInclusionMatrix r k)ᴴ)=
      c^n • (coordinateTensorMatrix n r k*(coordinateTensorMatrix n r k)ᴴ) := by
  simp only [tensorPower_mul,tensorPower_smul_complex,tensorPower_one,tensorPower_star,
    ← coordinateTensorMatrix_eq_tensorPower,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]

/-- The construction embedding is fixed. The input orbit U is arbitrary;
neither the channel nor its fallback is chosen from that input. -/
theorem rankPurificationChannel_flat_orbit (n k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) (c : ℂ) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (tensorPower n ((U.val*coordinateInclusionMatrix r k)*(c • (1 : Matrix (Fin r) (Fin r) ℂ))*
        (U.val*coordinateInclusionMatrix r k)ᴴ))=
      (tensorPower n (U.val*coordinateInclusionMatrix r k)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
        (haarPurificationChannel (A:=Fin r) n).toFun (tensorPower n (c • (1 : Matrix (Fin r) (Fin r) ℂ)))*
      (tensorPower n (U.val*coordinateInclusionMatrix r k)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
  let L := recursivePhysicalDecomposition n r
  have hL := (recursivePhysicalDecomposition_is_decomposition n r).1
  have hs := (recursivePhysicalDecomposition_is_decomposition n r).2
  let K := coordinateTensorMatrix n r k
  let X := c^n • (K*Kᴴ)
  have hX : momentSupport (Cloning.Compression.partialTrace
      (rectangularHaarMoment n (coordinateInclusionMatrix r k)))
      (partialTrace_rectangularHaarMoment_posSemidef n (coordinateInclusionMatrix r k))*X=X := by
    change momentSupport (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
      (c^n • (K*Kᴴ))=c^n • (K*Kᴴ)
    have hSK : momentSupport (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*K=K :=
      coordinateHaarSupport_mul_coordinateTensor L hL hs k
    rw [Matrix.mul_smul,← Matrix.mul_assoc,hSK]
  have ht : tensorPower n ((U.val*coordinateInclusionMatrix r k)*(c • (1 : Matrix (Fin r) (Fin r) ℂ))*
      (U.val*coordinateInclusionMatrix r k)ᴴ)=tensorPower n U.val*X*(tensorPower n U.val)ᴴ := by
    have he : (U.val*coordinateInclusionMatrix r k)*(c • (1 : Matrix (Fin r) (Fin r) ℂ))*
        (U.val*coordinateInclusionMatrix r k)ᴴ=
        U.val*(coordinateInclusionMatrix r k*(c • (1 : Matrix (Fin r) (Fin r) ℂ))*
          (coordinateInclusionMatrix r k)ᴴ)*U.valᴴ := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [he,tensorPower_mul,tensorPower_mul,tensorPower_star,coordinate_scalar_tensor_input]
  rw [ht,rankPurificationChannel_covariant_supported n (coordinateInclusionMatrix r k) b0 U X hX]
  change rectangularLeftTensor (B:=Fin r) n U.val*
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun (c^n • (K*Kᴴ))*
    (rectangularLeftTensor (B:=Fin r) n U.val)ᴴ=_
  rw [rankPurificationChannel_coordinate_scalar L hL hs,haarPurificationChannel_scalar_tensor]
  have hten : rectangularLeftTensor (B:=Fin r) n U.val*
      (K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))=
      tensorPower n (U.val*coordinateInclusionMatrix r k)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ) := by
    rw [rectangularLeftTensor,← Matrix.mul_kronecker_mul,Matrix.one_mul,tensorPower_mul]
    simp only [K,coordinateTensorMatrix_eq_tensorPower]
  calc
    _ = (rectangularLeftTensor (B:=Fin r) n U.val*(K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))*
        (c^n • rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ))*
        (rectangularLeftTensor (B:=Fin r) n U.val*(K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))ᴴ := by
      simp only [K,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hten]

end Cloning.PCTRankPurification
