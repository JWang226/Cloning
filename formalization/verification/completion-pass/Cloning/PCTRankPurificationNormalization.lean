import Cloning.PCTRankPurificationMoment
import Cloning.MatrixPartialTraceCovariance
import Mathlib.Analysis.Matrix.PosDef

/-! Spectral support normalization of the literal rectangular Haar moment. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Unitary
namespace Cloning.PCTRankPurification
open Cloning.PCTPurificationChannel Cloning.Compression Cloning.Channels
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
local instance normalizationMatrixCStar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- Inverse square root on positive eigenvalues, with zero on the null space. -/
def momentNormalizer (H : Matrix A A ℂ) (hH : H.PosSemidef) : Matrix A A ℂ :=
  conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary
    (Matrix.diagonal (fun a => ((Real.sqrt (hH.1.eigenvalues a))⁻¹ : ℂ)))

def momentSupport (H : Matrix A A ℂ) (hH : H.PosSemidef) : Matrix A A ℂ :=
  conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary
    (Matrix.diagonal (fun a => if hH.1.eigenvalues a=0 then 0 else (1 : ℂ)))

theorem momentNormalizer_star (H : Matrix A A ℂ) (hH : H.PosSemidef) :
    (momentNormalizer H hH)ᴴ=momentNormalizer H hH := by
  change star (momentNormalizer H hH)=momentNormalizer H hH
  unfold momentNormalizer
  rw [← map_star]
  congr 1
  ext a b
  by_cases hab : a=b
  · subst b; simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply,hab,Ne.symm hab]

theorem momentSupport_star (H : Matrix A A ℂ) (hH : H.PosSemidef) :
    (momentSupport H hH)ᴴ=momentSupport H hH := by
  change star (momentSupport H hH)=momentSupport H hH
  unfold momentSupport
  rw [← map_star]
  congr 1
  ext a b
  by_cases hab : a=b
  · subst b; simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply,hab,Ne.symm hab]

theorem momentSupport_mul_self (H : Matrix A A ℂ) (hH : H.PosSemidef) :
    momentSupport H hH*momentSupport H hH=momentSupport H hH := by
  unfold momentSupport
  rw [← map_mul,Matrix.diagonal_mul_diagonal]
  congr 1
  ext a b
  by_cases hab : a=b
  · subst b
    simp
  · simp [Matrix.diagonal_apply_ne _ hab]

theorem momentNormalizer_normalizes (H : Matrix A A ℂ) (hH : H.PosSemidef) :
    momentNormalizer H hH*H*(momentNormalizer H hH)ᴴ=momentSupport H hH := by
  rw [momentNormalizer_star]
  conv_lhs => arg 1; arg 2; rw [hH.1.spectral_theorem]
  unfold momentNormalizer momentSupport
  rw [← map_mul,← map_mul,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  apply congrArg Matrix.diagonal
  funext a
  change ((Real.sqrt (hH.1.eigenvalues a))⁻¹ : ℂ)*(hH.1.eigenvalues a : ℂ)*
    ((Real.sqrt (hH.1.eigenvalues a))⁻¹ : ℂ) = if hH.1.eigenvalues a=0 then 0 else 1
  by_cases ha : hH.1.eigenvalues a=0
  · simp [ha]
  · rw [if_neg ha]
    have hs : Real.sqrt (hH.1.eigenvalues a) ≠ 0 :=
      (Real.sqrt_pos.2 (lt_of_le_of_ne (hH.eigenvalues_nonneg a) (Ne.symm ha))).ne'
    have he := Real.sq_sqrt (hH.eigenvalues_nonneg a)
    have hz : ((Real.sqrt (hH.1.eigenvalues a))⁻¹ : ℝ)*hH.1.eigenvalues a*
        (Real.sqrt (hH.1.eigenvalues a))⁻¹=1 := by
      field_simp
      nlinarith [he]
    exact_mod_cast hz

/-- Normalize a positive bipartite moment on its actual input support. -/
def normalizedMoment (R : Matrix (A×B) (A×B) ℂ)
    (hH : (partialTrace R).PosSemidef) : Matrix (A×B) (A×B) ℂ :=
  (momentNormalizer (partialTrace R) hH ⊗ₖ (1 : Matrix B B ℂ))*R*
    (momentNormalizer (partialTrace R) hH ⊗ₖ (1 : Matrix B B ℂ))ᴴ

theorem normalizedMoment_posSemidef (R : Matrix (A×B) (A×B) ℂ)
    (hR : R.PosSemidef) (hH : (partialTrace R).PosSemidef) :
    (normalizedMoment R hH).PosSemidef := hR.mul_mul_conjTranspose_same _

theorem partialTrace_normalizedMoment (R : Matrix (A×B) (A×B) ℂ)
    (hH : (partialTrace R).PosSemidef) :
    partialTrace (normalizedMoment R hH)=momentSupport (partialTrace R) hH := by
  rw [normalizedMoment,partialTrace_tensor_conjugation _ _ _ (by simp)]
  exact momentNormalizer_normalizes _ hH

variable [Nonempty A]
theorem partialTrace_rectangularHaarMoment_posSemidef (n : ℕ) (J : Matrix A B ℂ) :
    (partialTrace (rectangularHaarMoment n J)).PosSemidef := by
  rw [partialTrace_rectangularHaarMoment]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg
  intro U
  change 0 ≤ tensorPower n (U.val*(J*Jᴴ)*U.valᴴ)
  have he : (U.val*(J*Jᴴ)*U.valᴴ)=(U.val*J)*(U.val*J)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he,tensorPower_mul,tensorPower_star]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).nonneg

/-- An explicit all-input CPTP rectangular purification map. Its normalization
and completion are proved from the actual Haar moment and its spectrum. -/
def rankPurificationChannel (n : ℕ) (J : Matrix A B ℂ)
    (b0 : (Fin n → A)×(Fin n → B)) :
    MatrixChannel (Fin n → A) ((Fin n → A)×(Fin n → B)) :=
  supportedPurificationChannel
    (normalizedMoment (rectangularHaarMoment n J) (partialTrace_rectangularHaarMoment_posSemidef n J))
    (normalizedMoment_posSemidef _ (rectangularHaarMoment_posSemidef n J) _)
    (momentSupport _ (partialTrace_rectangularHaarMoment_posSemidef n J))
    (momentSupport_star _ _) (momentSupport_mul_self _ _)
    (partialTrace_normalizedMoment _ _) b0

end Cloning.PCTRankPurification
