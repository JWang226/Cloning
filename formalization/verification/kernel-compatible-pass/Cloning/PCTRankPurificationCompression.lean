import Cloning.PCTRankPurificationMomentComparison
import Cloning.PCTRankPurificationBlockHaar

/-! The actual normalized rectangular Haar moment restricts exactly to the
smaller physical purification moment. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.TensorLie Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {n r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

variable (L : List (PhysicalHighestTensor n r))
  (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
    (fun i => (L.get i).sector.subtypeₗᵢ))
  (hspan : (⨆i : Fin L.length,(L.get i).sector)=⊤)

include hL hspan in
theorem coordinateNormalizedMoment_compression (k : ℕ) :
    ((coordinateTensorMatrix n r k)ᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
      normalizedMoment (rectangularHaarMoment n (coordinateInclusionMatrix r k))
        (partialTrace_rectangularHaarMoment_posSemidef n (coordinateInclusionMatrix r k))*
      ((coordinateTensorMatrix n r k)ᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ=
      rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ) := by
  let K := coordinateTensorMatrix n r k
  let N := momentNormalizer (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)
  let f (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :=
    tensorPower n (U.val*coordinateInclusionMatrix r k)
  have hf : Integrable (fun U => matrixMoment (f U)) unitaryHaar :=
    integrable_rectangularMoment n (coordinateInclusionMatrix r k)
  have hM := matrixMomentIntegral_mul unitaryHaar f hf (Kᴴ*N)
    (1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)
  have hf' (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
      Kᴴ*N*f U*1=normalizedCoordinateAction k N U := by
    simp only [f,tensorPower_mul,← coordinateTensorMatrix_eq_tensorPower,Matrix.mul_one,
      normalizedCoordinateAction,K,Matrix.mul_assoc]
  simp_rw [hf'] at hM
  have hm : matrixMomentIntegral unitaryHaar f=rectangularHaarMoment n (coordinateInclusionMatrix r k) := rfl
  rw [hm,Matrix.transpose_one] at hM
  have he := normalizedCoordinateAction_moment L hL hspan k N (momentNormalizer_star _ _)
    (coordinateHaarNormalizer_mul_liftEmbedding L hL hspan k)
  have hs : matrixMomentIntegral unitaryHaar (fun V : unitary (Matrix (Fin r) (Fin r) ℂ) => tensorPower n V.val)=
      rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ) := by
    simp only [rectangularHaarMoment,Matrix.mul_one,rectangularMoment_eq_matrixMoment,matrixMomentIntegral]
  rw [hs] at he
  rw [← he,hM]
  change (Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
    ((N⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*rectangularHaarMoment n (coordinateInclusionMatrix r k)*(N⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ)*(Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ=_
  have hten : (Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*(N⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))=(Kᴴ*N)⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ) := by
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
  calc
    _ = ((Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*(N⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))*rectangularHaarMoment n (coordinateInclusionMatrix r k)*
        ((Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*(N⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hten]

end Cloning.PCTRankPurification
