import Cloning.PCTRankPurificationBlockMatrices

/-! Literal support projections for the rectangular coordinate inclusion. -/
noncomputable section
open scoped BigOperators Classical Matrix
namespace Cloning.TensorLie
open Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem coordinateInclusionMatrix_isometry (r k : ℕ) :
    (coordinateInclusionMatrix r k)ᴴ*coordinateInclusionMatrix r k=1 := by
  ext a b
  simp [coordinateInclusionMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm]

theorem coordinateInclusionMatrix_projection (r k : ℕ) :
    coordinateInclusionMatrix r k*(coordinateInclusionMatrix r k)ᴴ=coordinateSupportMatrix r k := by
  ext a b
  by_cases ha : a.val<r
  · let a0 : Fin r := ⟨a.val,ha⟩
    have he : a=Fin.castAdd k a0 := Fin.ext rfl
    rw [he]
    simp [coordinateInclusionMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      coordinateSupportMatrix,Matrix.diagonal_apply,a0.isLt,eq_comm]
    rw [Finset.sum_eq_single a0]
    · simp
    · intro x hx hxa
      simp [hxa]
    · simp
  · have hz (z : Fin r) : a≠Fin.castAdd k z := by
      intro he
      apply ha
      rw [he]
      exact z.isLt
    simp [coordinateInclusionMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      coordinateSupportMatrix,Matrix.diagonal_apply,hz,ha]

theorem coordinateTensorMatrix_isometry (n r k : ℕ) :
    (coordinateTensorMatrix n r k)ᴴ*coordinateTensorMatrix n r k=1 := by
  rw [coordinateTensorMatrix_eq_tensorPower,← tensorPower_star,← tensorPower_mul,
    coordinateInclusionMatrix_isometry,tensorPower_one]

theorem coordinateTensorMatrix_projection (n r k : ℕ) :
    coordinateTensorMatrix n r k*(coordinateTensorMatrix n r k)ᴴ=
      tensorPower n (coordinateSupportMatrix r k) := by
  rw [coordinateTensorMatrix_eq_tensorPower,← tensorPower_star,← tensorPower_mul,
    coordinateInclusionMatrix_projection]

end Cloning.TensorLie
