import Cloning.PCTRankPurificationCompression
import Cloning.PCTRankPurificationBlockSupport
import Cloning.PCTRankPurificationBlockCoordinate
import Cloning.PCTRankPurificationInvariant

/-! Exact flat-input action of the fixed all-input rectangular purifier. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
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
theorem rankPurificationChannel_coordinate_projection (k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r)) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (coordinateTensorMatrix n r k*(coordinateTensorMatrix n r k)ᴴ)=
      (coordinateTensorMatrix n r k⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
        rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ)*
      (coordinateTensorMatrix n r k⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
  let K := coordinateTensorMatrix n r k
  let P := K*Kᴴ
  let R := normalizedMoment (rectangularHaarMoment n (coordinateInclusionMatrix r k))
    (partialTrace_rectangularHaarMoment_posSemidef n (coordinateInclusionMatrix r k))
  have hR : R.PosSemidef := normalizedMoment_posSemidef _ (rectangularHaarMoment_posSemidef _ _) _
  have hP : P*P=P := by
    dsimp only [P]
    rw [Matrix.mul_assoc,← Matrix.mul_assoc Kᴴ,coordinateTensorMatrix_isometry,Matrix.one_mul]
  have hPS : Pᴴ=P := by simp only [P,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have hc : Commute R (P⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)) := by
    dsimp only [P,K]
    rw [coordinateTensorMatrix_projection]
    exact normalized_rectangularHaarMoment_commute_hermitian n (coordinateInclusionMatrix r k)
      (coordinateSupportMatrix r k) coordinateSupportMatrix_star
  have hact := rankPurificationChannel_apply_coordinate_supported L hL hspan k b0
    (1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)
  simp only [Matrix.mul_one] at hact
  rw [hact]
  change purificationMap R P=_
  rw [← hP,purificationMap_square hR P hc]
  have hcompress := coordinateNormalizedMoment_compression L hL hspan k
  change (Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*R*(Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ=_ at hcompress
  rw [← hcompress]
  have hten : (K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*(Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))=P⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ) := by
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
  change (P⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*R*(P⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))=_
  calc
    _=(P⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*R*(P⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
      rw [Matrix.conjTranspose_kronecker,hPS,Matrix.conjTranspose_one]
    _=((K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*(Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))*R*((K⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*(Kᴴ⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ)))ᴴ := by rw [hten]
    _=_ := by simp only [K,Matrix.conjTranspose_mul,Matrix.mul_assoc]

include hL hspan in
theorem rankPurificationChannel_coordinate_scalar (k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r)) (c : ℂ) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (c • (coordinateTensorMatrix n r k*(coordinateTensorMatrix n r k)ᴴ))=
      (coordinateTensorMatrix n r k⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
        (c • rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ))*
      (coordinateTensorMatrix n r k⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
  rw [(rankPurificationChannel n (coordinateInclusionMatrix r k) b0).map_smul,
    rankPurificationChannel_coordinate_projection L hL hspan]
  simp only [Matrix.mul_smul,Matrix.smul_mul]

end Cloning.PCTRankPurification
