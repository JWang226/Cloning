import Cloning.PCTRankPurificationInvariant

/-! Covariance of the single completed rectangular purifier on its actual
Haar support. No covariance of the arbitrary fallback state is required. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Cloning.PCTRankPurification
open Matrix Cloning.PCTPurificationChannel Cloning.Compression Cloning.MatrixFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
local instance covarianceMatrixCStar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- Exact conjugation covariance of the square-root sandwich from actual
commutation with the input unitary and its adjoint. -/
theorem purificationMap_conjugate_of_commute (R : Matrix (A×B) (A×B) ℂ)
    (V X : Matrix A A ℂ)
    (hV : Commute R (V ⊗ₖ (1 : Matrix B B ℂ)))
    (hVs : Commute R (Vᴴ ⊗ₖ (1 : Matrix B B ℂ))) :
    purificationMap R (V*X*Vᴴ)=
      (V ⊗ₖ (1 : Matrix B B ℂ))*purificationMap R X*(V ⊗ₖ (1 : Matrix B B ℂ))ᴴ := by
  have hs : Commute (CFC.sqrt R) (V ⊗ₖ (1 : Matrix B B ℂ)) := hV.cfcₙ_nnreal NNReal.sqrt
  have hss : Commute (CFC.sqrt R) ((V ⊗ₖ (1 : Matrix B B ℂ))ᴴ) := by
    simpa only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one] using
      hVs.cfcₙ_nnreal NNReal.sqrt
  have ht : (V*X*Vᴴ) ⊗ₖ (1 : Matrix B B ℂ)=
      (V ⊗ₖ (1 : Matrix B B ℂ))*(X ⊗ₖ (1 : Matrix B B ℂ))*(V ⊗ₖ (1 : Matrix B B ℂ))ᴴ := by
    simp only [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul,Matrix.one_mul]
  unfold purificationMap
  rw [ht]
  calc
    _ = (CFC.sqrt R*(V ⊗ₖ (1 : Matrix B B ℂ)))*(X ⊗ₖ (1 : Matrix B B ℂ))*
        ((V ⊗ₖ (1 : Matrix B B ℂ))ᴴ*CFC.sqrt R) := by noncomm_ring
    _ = ((V ⊗ₖ (1 : Matrix B B ℂ))*CFC.sqrt R)*(X ⊗ₖ (1 : Matrix B B ℂ))*
        (CFC.sqrt R*(V ⊗ₖ (1 : Matrix B B ℂ))ᴴ) := by rw [hs.eq,← hss.eq]
    _ = _ := by noncomm_ring

variable [Nonempty A]

/-- The derived support is preserved by every physical unitary tensor power. -/
theorem rankPurificationSupport_conjugate (n : ℕ) (J : Matrix A B ℂ)
    (U : unitary (Matrix A A ℂ)) (X : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hX : momentSupport (partialTrace (rectangularHaarMoment n J))
      (partialTrace_rectangularHaarMoment_posSemidef n J)*X=X) :
    momentSupport (partialTrace (rectangularHaarMoment n J))
      (partialTrace_rectangularHaarMoment_posSemidef n J)*
      (tensorPower n U.val*X*(tensorPower n U.val)ᴴ)=
      tensorPower n U.val*X*(tensorPower n U.val)ᴴ := by
  have hc := momentSupport_commutes (partialTrace (rectangularHaarMoment n J))
    (partialTrace_rectangularHaarMoment_posSemidef n J) (tensorPower n U.val)
    (partialTrace_rectangularHaarMoment_commute_unitary n J U).eq
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hc,Matrix.mul_assoc _ _ X,hX]

/-- The fixed all-input channel rotates exactly on every supported input.
The same channel and same fallback word occur on both sides. -/
theorem rankPurificationChannel_covariant_supported (n : ℕ) (J : Matrix A B ℂ)
    (b0 : (Fin n → A)×(Fin n → B))
    (U : unitary (Matrix A A ℂ)) (X : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hX : momentSupport (partialTrace (rectangularHaarMoment n J))
      (partialTrace_rectangularHaarMoment_posSemidef n J)*X=X) :
    (rankPurificationChannel n J b0).toFun (tensorPower n U.val*X*(tensorPower n U.val)ᴴ)=
      rectangularLeftTensor (B := B) n U.val*(rankPurificationChannel n J b0).toFun X*
        (rectangularLeftTensor (B := B) n U.val)ᴴ := by
  let R := normalizedMoment (rectangularHaarMoment n J)
    (partialTrace_rectangularHaarMoment_posSemidef n J)
  have ha (Y : Matrix (Fin n → A) (Fin n → A) ℂ)
      (hY : momentSupport (partialTrace (rectangularHaarMoment n J))
        (partialTrace_rectangularHaarMoment_posSemidef n J)*Y=Y) :
      (rankPurificationChannel n J b0).toFun Y=purificationMap R Y :=
    supportedPurificationChannel_apply_supported _ _ _ _ _ _ b0 Y hY
  rw [ha _ (rankPurificationSupport_conjugate n J U X hX),ha X hX]
  apply purificationMap_conjugate_of_commute
  · exact normalized_rectangularHaarMoment_commute_unitary n J U
  · have hh := normalized_rectangularHaarMoment_commute_unitary n J (star U)
    simpa only [rectangularLeftTensor,Unitary.coe_star,Matrix.star_eq_conjTranspose,tensorPower_star] using hh

end Cloning.PCTRankPurification
