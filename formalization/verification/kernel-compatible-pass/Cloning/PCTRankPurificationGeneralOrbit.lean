import Cloning.PCTRankPurificationGeneralAction
import Cloning.PhysicalFlatGrassmannIsometry

/-! The same fixed rectangular purifier works on every embedded positive input,
with arbitrary support and arbitrary internal spectrum. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Cloning.PCTRankPurification
open Cloning.TensorLie Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
variable {r : ℕ} [NeZero r]
local instance generalOrbitAmbientNeZero (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

theorem rankPurificationChannel_positive_orbit (n k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ))
    (ρ : Matrix (Fin r) (Fin r) ℂ) (hρ : ρ.PosSemidef) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (tensorPower n ((U.val*coordinateInclusionMatrix r k)*ρ*
        (U.val*coordinateInclusionMatrix r k)ᴴ))=
      (tensorPower n (U.val*coordinateInclusionMatrix r k)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
        (haarPurificationChannel (A:=Fin r) n).toFun (tensorPower n ρ)*
      (tensorPower n (U.val*coordinateInclusionMatrix r k)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
  let L := recursivePhysicalDecomposition n r
  have hL := (recursivePhysicalDecomposition_is_decomposition n r).1
  have hs := (recursivePhysicalDecomposition_is_decomposition n r).2
  let K := coordinateTensorMatrix n r k
  let X := K*tensorPower n ρ*Kᴴ
  have hX : momentSupport (Cloning.Compression.partialTrace
      (rectangularHaarMoment n (coordinateInclusionMatrix r k)))
      (partialTrace_rectangularHaarMoment_posSemidef n (coordinateInclusionMatrix r k))*X=X := by
    change momentSupport (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
      (K*tensorPower n ρ*Kᴴ)=_
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,coordinateHaarSupport_mul_coordinateTensor L hL hs]
  have ht : tensorPower n ((U.val*coordinateInclusionMatrix r k)*ρ*
      (U.val*coordinateInclusionMatrix r k)ᴴ)=tensorPower n U.val*X*(tensorPower n U.val)ᴴ := by
    simp only [X,K,tensorPower_mul,tensorPower_star,Matrix.conjTranspose_mul,
      ← coordinateTensorMatrix_eq_tensorPower,Matrix.mul_assoc]
  rw [ht,rankPurificationChannel_covariant_supported n (coordinateInclusionMatrix r k) b0 U X hX]
  have hact := rankPurificationChannel_coordinate_positive n k b0 ρ hρ
  simp only [tensorPower_mul,tensorPower_star,← coordinateTensorMatrix_eq_tensorPower] at hact
  change rectangularLeftTensor (B:=Fin r) n U.val*
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun X*
    (rectangularLeftTensor (B:=Fin r) n U.val)ᴴ=_
  rw [hact]
  have hten : rectangularLeftTensor (B:=Fin r) n U.val*
      (K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))=
      tensorPower n (U.val*coordinateInclusionMatrix r k)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ) := by
    rw [rectangularLeftTensor,← Matrix.mul_kronecker_mul,Matrix.one_mul,tensorPower_mul]
    simp only [K,coordinateTensorMatrix_eq_tensorPower]
  calc
    _ = (rectangularLeftTensor (B:=Fin r) n U.val*(K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))*
        (haarPurificationChannel (A:=Fin r) n).toFun (tensorPower n ρ)*
        (rectangularLeftTensor (B:=Fin r) n U.val*(K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))ᴴ := by
      simp only [K,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hten]

/-- Both the construction embedding and fallback are fixed before the input
isometry and the input spectrum are supplied. -/
theorem rankPurificationChannel_embedded_positive (n k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (J : Matrix (Fin (r+k)) (Fin r) ℂ) (hJ : Jᴴ*J=1)
    (ρ : Matrix (Fin r) (Fin r) ℂ) (hρ : ρ.PosSemidef) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (tensorPower n (J*ρ*Jᴴ))=
      (tensorPower n J⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
        (haarPurificationChannel (A:=Fin r) n).toFun (tensorPower n ρ)*
      (tensorPower n J⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
  obtain ⟨U,hU⟩ := Cloning.PhysicalFlatGrassmann.exists_unitary_isometry r k J hJ
  change J=U.val*coordinateInclusionMatrix r k at hU
  rw [hU]
  exact rankPurificationChannel_positive_orbit n k b0 U ρ hρ

end Cloning.PCTRankPurification
