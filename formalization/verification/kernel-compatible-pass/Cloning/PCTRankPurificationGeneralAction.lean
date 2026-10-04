import Cloning.PCTRankPurificationFlatOrbit

/-! The fixed rectangular purifier acts correctly on every positive density
supported by the coordinate rank bound, including nonflat and singular inputs. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Cloning.PCTRankPurification
open Cloning.TensorLie Cloning.PCTPurificationChannel Cloning.MatrixFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {r : ℕ} [NeZero r]
local instance generalActionAmbientNeZero (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

/-- The supported input can have any positive spectrum. No scalar or
full-rank hypothesis is imposed on the smaller density. -/
theorem rankPurificationChannel_coordinate_positive (n k : ℕ)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (ρ : Matrix (Fin r) (Fin r) ℂ) (hρ : ρ.PosSemidef) :
    (rankPurificationChannel n (coordinateInclusionMatrix r k) b0).toFun
      (tensorPower n (coordinateInclusionMatrix r k*ρ*(coordinateInclusionMatrix r k)ᴴ))=
      (coordinateTensorMatrix n r k⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))*
        (haarPurificationChannel (A:=Fin r) n).toFun (tensorPower n ρ)*
      (coordinateTensorMatrix n r k⊗ₖ(1 : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ))ᴴ := by
  let L := recursivePhysicalDecomposition n r
  have hL := (recursivePhysicalDecomposition_is_decomposition n r).1
  have hs := (recursivePhysicalDecomposition_is_decomposition n r).2
  let K := coordinateTensorMatrix n r k
  let S := tensorPower n (CFC.sqrt ρ)
  let X := K*S*Kᴴ
  let R := normalizedMoment (rectangularHaarMoment n (coordinateInclusionMatrix r k))
    (partialTrace_rectangularHaarMoment_posSemidef n (coordinateInclusionMatrix r k))
  let I : Matrix (Fin n → Fin r) (Fin n → Fin r) ℂ := 1
  have hR : R.PosSemidef := normalizedMoment_posSemidef _ (rectangularHaarMoment_posSemidef _ _) _
  have hSS : S*S=tensorPower n ρ := by
    dsimp only [S]
    rw [← tensorPower_mul,sqrt_mul_self hρ]
  have hSstar : Sᴴ=S := by
    dsimp only [S]
    rw [← tensorPower_star,sqrt_conjTranspose]
  have hXtensor : X=tensorPower n
      (coordinateInclusionMatrix r k*CFC.sqrt ρ*(coordinateInclusionMatrix r k)ᴴ) := by
    simp only [X,K,S,tensorPower_mul,tensorPower_star,← coordinateTensorMatrix_eq_tensorPower]
  have hXsquare : X*X=K*tensorPower n ρ*Kᴴ := by
    calc
      _=K*S*(Kᴴ*K)*S*Kᴴ := by simp only [X,Matrix.mul_assoc]
      _=_ := by rw [coordinateTensorMatrix_isometry,Matrix.mul_one,Matrix.mul_assoc K S S, hSS]
  have hc : Commute R (X⊗ₖI) := by
    rw [hXtensor]
    exact normalized_rectangularHaarMoment_commute_hermitian n (coordinateInclusionMatrix r k)
      _ ((sqrt_posSemidef ρ).mul_mul_conjTranspose_same _).isHermitian
  have hsmall : (haarPurificationChannel (A:=Fin r) n).toFun (tensorPower n ρ)=
      (S⊗ₖI)*rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ)*(S⊗ₖI) := by
    rw [haarPurificationChannel_apply,← hSS,
      purificationMap_square (haarMoment_posSemidef n) S
        (haarMoment_commute_hermitian n _ (sqrt_posSemidef ρ).isHermitian)]
    rw [rectangularHaarMoment_one]
  have hcompress := coordinateNormalizedMoment_compression L hL hs k
  change (Kᴴ⊗ₖI)*R*(Kᴴ⊗ₖI)ᴴ=rectangularHaarMoment n (1 : Matrix (Fin r) (Fin r) ℂ) at hcompress
  have hten : (K⊗ₖI)*(S⊗ₖI)*(Kᴴ⊗ₖI)=X⊗ₖI := by
    simp only [← Matrix.mul_kronecker_mul, I, Matrix.one_mul, X]
  have hleft : (Kᴴ⊗ₖI)ᴴ=(K⊗ₖI) := by
    simp only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_conjTranspose,I,Matrix.conjTranspose_one]
  have hright : (K⊗ₖI)ᴴ=(Kᴴ⊗ₖI) := by
    simp only [Matrix.conjTranspose_kronecker,I,Matrix.conjTranspose_one]
  simp only [tensorPower_mul,tensorPower_star,← coordinateTensorMatrix_eq_tensorPower]
  rw [rankPurificationChannel_apply_coordinate_supported L hL hs]
  change purificationMap R (K*tensorPower n ρ*Kᴴ)=_
  rw [← hXsquare,purificationMap_square hR X hc,hsmall,← hcompress,hleft]
  change (X⊗ₖI)*R*(X⊗ₖI)=(K⊗ₖI)*((S⊗ₖI)*((Kᴴ⊗ₖI)*R*(K⊗ₖI))*(S⊗ₖI))*(K⊗ₖI)ᴴ
  rw [hright,← hten]
  simp only [Matrix.mul_assoc]

end Cloning.PCTRankPurification
