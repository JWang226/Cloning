import Cloning.WeylCharacterAlternantSubsets
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Vandermonde

/-! Exact Euler spectral calculus for finite alternants. -/
noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false

def euler {d : ℕ} (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  (LinearMap.mulLeft ℂ (X i)).comp (pderiv i).toLinearMap

@[simp] theorem euler_apply {d : ℕ} (i : Fin d) (P : MvPolynomial (Fin d) ℂ) :
    euler i P = X i * pderiv i P := rfl

@[simp] theorem euler_monomial {d : ℕ} (i : Fin d) (m : Fin d →₀ ℕ) (c : ℂ) :
    euler i (monomial m c) = monomial m ((m i : ℂ) * c) := by
  rw [euler_apply, X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul ℂ, smul_monomial]
  rfl

theorem coeff_euler {d : ℕ} (i : Fin d) (P : MvPolynomial (Fin d) ℂ) (m : Fin d →₀ ℕ) :
    coeff m (euler i P) = (m i : ℂ) * coeff m P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]
  | monomial n c =>
    rw [euler_monomial]
    by_cases h : n = m
    · subst n; simp
    · simp [coeff_monomial, h]

def eulerSquares {d : ℕ} : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i : Fin d, (euler i).comp (euler i)

@[simp] theorem eulerSquares_apply {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    eulerSquares P = ∑ i : Fin d, X i * pderiv i (X i * pderiv i P) := by
  simp [eulerSquares]

theorem coeff_eulerSquares {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (m : Fin d →₀ ℕ) :
    coeff m (eulerSquares P) = (∑ i, (m i : ℂ)^2) * coeff m P := by
  simp only [eulerSquares, LinearMap.sum_apply, LinearMap.comp_apply, coeff_sum, coeff_euler]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem support_eulerSquares_eigenvalue {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (c : ℂ)
    (h : eulerSquares P = c • P) (m : Fin d →₀ ℕ) (hm : coeff m P ≠ 0) :
    ∑ i, (m i : ℂ)^2 = c := by
  have he := congrArg (coeff m) h
  rw [coeff_eulerSquares, coeff_smul, smul_eq_mul] at he
  exact mul_right_cancel₀ hm he

def exponentOf {d : ℕ} (a : Fin d → ℕ) : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponentOf_apply {d : ℕ} (a : Fin d → ℕ) (i : Fin d) :
    exponentOf a i = a i := rfl

theorem prod_X_pow_eq {d : ℕ} (a : Fin d → ℕ) :
    (∏ i, (X i : MvPolynomial (Fin d) ℂ) ^ a i) = monomial (exponentOf a) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  rfl

def alternant {d : ℕ} (a : Fin d → ℕ) : MvPolynomial (Fin d) ℂ :=
  Matrix.det (fun i j : Fin d ↦ X i ^ a j)

theorem alternant_expansion {d : ℕ} (a : Fin d → ℕ) :
    alternant a = ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) • monomial (exponentOf (a ∘ σ.symm)) 1 := by
  rw [alternant, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hprod : (∏ i : Fin d, (X (σ i) : MvPolynomial (Fin d) ℂ) ^ a i) =
      ∏ i : Fin d, X i ^ a (σ.symm i) := by
    simpa using (Equiv.prod_comp σ (fun i ↦ (X i : MvPolynomial (Fin d) ℂ) ^ a (σ.symm i)))
  rw [hprod, prod_X_pow_eq]
  simp only [Units.smul_def, Int.cast_smul_eq_zsmul]
  rfl

theorem eulerSquares_alternant {d : ℕ} (a : Fin d → ℕ) :
    eulerSquares (alternant a) = (∑ i, (a i : ℂ)^2) • alternant a := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_eulerSquares, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m (alternant a) = 0
  · simp [hm]
  have hex : ∃ σ : Equiv.Perm (Fin d), m = exponentOf (a ∘ σ.symm) := by
    by_contra! hh
    apply hm
    rw [alternant_expansion, coeff_sum]
    apply Finset.sum_eq_zero
    intro σ hσ
    simp [coeff_smul, coeff_monomial, Ne.symm (hh σ)]
  obtain ⟨σ, rfl⟩ := hex
  simp only [exponentOf_apply, Function.comp_apply]
  rw [Equiv.sum_comp σ.symm (fun i ↦ (a i : ℂ)^2)]

/-- The usual Vandermonde, with increasing columns, is an exact Euler-square
 eigenvector. Multiplying by a scalar sign gives the reversed denominator. -/
theorem eulerSquares_vandermonde (d : ℕ) :
    eulerSquares ((Matrix.vandermonde (fun i : Fin d ↦ (X i : MvPolynomial (Fin d) ℂ))).det) =
      (∑ i : Fin d, (i.val : ℂ)^2) •
        (Matrix.vandermonde (fun i : Fin d ↦ (X i : MvPolynomial (Fin d) ℂ))).det :=
  eulerSquares_alternant (fun i : Fin d ↦ i.val)

end Cloning.WeylCharacter
