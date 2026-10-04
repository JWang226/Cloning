import Cloning.PCTRankPurificationNormalization

/-! Elementary finite spectral calculus for the actual moment normalizer. -/
noncomputable section
open scoped BigOperators Classical Matrix ComplexOrder
open Matrix Unitary
namespace Cloning.PCTRankPurification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [DecidableEq A]

def momentSpectral (H : Matrix A A ℂ) (hH : H.PosSemidef) (f : ℝ → ℂ) : Matrix A A ℂ :=
  conjStarAlgAut ℂ _ hH.1.eigenvectorUnitary (Matrix.diagonal (fun a => f (hH.1.eigenvalues a)))

theorem diagonal_function_commutes (lambda : A → ℝ) (f : ℝ → ℂ) (X : Matrix A A ℂ)
    (hX : Matrix.diagonal (fun a => (lambda a : ℂ))*X=X*Matrix.diagonal (fun a => (lambda a : ℂ))) :
    Matrix.diagonal (fun a => f (lambda a))*X=X*Matrix.diagonal (fun a => f (lambda a)) := by
  ext a b
  have hab := congrArg (fun T : Matrix A A ℂ => T a b) hX
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at hab ⊢
  by_cases he : lambda a=lambda b
  · rw [he]; exact mul_comm _ _
  · have hn : (lambda a : ℂ)-(lambda b : ℂ)≠0 := by
      exact sub_ne_zero.mpr (fun hh => he (Complex.ofReal_injective hh))
    have hz : ((lambda a : ℂ)-(lambda b : ℂ))*X a b=0 := by linear_combination hab
    have hzero := (mul_eq_zero.mp hz).resolve_left hn
    simp [hzero]

theorem momentSpectral_commutes (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (f : ℝ → ℂ) (X : Matrix A A ℂ) (hX : H*X=X*H) :
    momentSpectral H hH f*X=X*momentSpectral H hH f := by
  let C := conjStarAlgAut ℂ (Matrix A A ℂ) hH.1.eigenvectorUnitary
  have hs : H=C (Matrix.diagonal (fun a => (hH.1.eigenvalues a : ℂ))) := hH.1.spectral_theorem
  have hCH : C.symm H=Matrix.diagonal (fun a => (hH.1.eigenvalues a : ℂ)) :=
    (congrArg C.symm hs).trans (C.symm_apply_apply _)
  have he := congrArg C.symm hX
  simp only [map_mul,hCH] at he
  have hf := diagonal_function_commutes hH.1.eigenvalues f (C.symm X) he
  have hh := congrArg C hf
  simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using hh

theorem momentNormalizer_commutes (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (X : Matrix A A ℂ) (hX : H*X=X*H) :
    momentNormalizer H hH*X=X*momentNormalizer H hH :=
  momentSpectral_commutes H hH (fun t => ((Real.sqrt t)⁻¹ : ℂ)) X hX

theorem momentSupport_commutes (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (X : Matrix A A ℂ) (hX : H*X=X*H) :
    momentSupport H hH*X=X*momentSupport H hH :=
  momentSpectral_commutes H hH (fun t => if t=0 then 0 else 1) X hX

theorem diagonal_function_left_eigenrelation (lambda : A → ℝ) (f : ℝ → ℂ)
    (X : Matrix A A ℂ) (c : ℝ)
    (hX : Matrix.diagonal (fun a => (lambda a : ℂ))*X=(c : ℂ) • X) :
    Matrix.diagonal (fun a => f (lambda a))*X=f c • X := by
  ext a b
  have hab := congrArg (fun T : Matrix A A ℂ => T a b) hX
  simp only [Matrix.diagonal_mul,Matrix.smul_apply,smul_eq_mul] at hab ⊢
  by_cases he : lambda a=c
  · rw [he]
  · have hn : (lambda a : ℂ)-(c : ℂ)≠0 :=
      sub_ne_zero.mpr (fun hh => he (Complex.ofReal_injective hh))
    have hz : ((lambda a : ℂ)-(c : ℂ))*X a b=0 := by linear_combination hab
    simp [(mul_eq_zero.mp hz).resolve_left hn]

theorem momentSpectral_left_eigenrelation (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (f : ℝ → ℂ) (X : Matrix A A ℂ) (c : ℝ) (hX : H*X=(c : ℂ) • X) :
    momentSpectral H hH f*X=f c • X := by
  let C := conjStarAlgAut ℂ (Matrix A A ℂ) hH.1.eigenvectorUnitary
  have hs : H=C (Matrix.diagonal (fun a => (hH.1.eigenvalues a : ℂ))) := hH.1.spectral_theorem
  have hCH : C.symm H=Matrix.diagonal (fun a => (hH.1.eigenvalues a : ℂ)) :=
    (congrArg C.symm hs).trans (C.symm_apply_apply _)
  have he := congrArg C.symm hX
  simp only [map_mul,map_smul,hCH] at he
  have hf := diagonal_function_left_eigenrelation hH.1.eigenvalues f (C.symm X) c he
  have hh := congrArg C hf
  simpa only [map_mul,map_smul,StarAlgEquiv.apply_symm_apply] using hh

end Cloning.PCTRankPurification
