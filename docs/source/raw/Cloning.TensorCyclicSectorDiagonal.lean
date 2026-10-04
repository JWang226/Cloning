import Cloning.TensorCyclicSectorTensorPower
import Cloning.PCTPurificationInvariance

/-!
# From Cartan commutation to literal diagonal tensor powers

An operator commuting with the actual Cartan generators has zero matrix
coefficients between different occupation vectors. The actual tensor power
of any complex diagonal matrix is constant on each such occupation space.
No invertibility, positivity, or nonzero-coordinate condition is imposed.
-/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.PCTPurificationChannel
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- A word's diagonal multiplier depends only on its occupation vector. -/
theorem word_product_eq_occupancy (D : Fin d → ℂ) (w : Fin n → Fin d) :
    (∏ t, D (w t)) = ∏ a, D a ^ occupancy w a := by
  simpa only [Finset.prod_const, occupancy] using
    (Finset.prod_fiberwise' Finset.univ w D).symm

/-- The literal diagonal tensor power is a diagonal operator in the word basis. -/
theorem tensorOperator_diagonal_apply (D : Fin d → ℂ)
    (x : TensorRegister n (Fin d)) (w : Fin n → Fin d) :
    tensorOperator n (Matrix.diagonal D) x w = (∏ t, D (w t)) * x w := by
  have hdiag : tensorPower n (Matrix.diagonal D) =
      Matrix.diagonal (fun v : Fin n → Fin d => ∏ t, D (v t)) := by
    ext v u
    by_cases h : v = u
    · subst u
      simp [tensorPower]
    · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
      rw [Matrix.diagonal_apply_ne _ h]
      exact Finset.prod_eq_zero (Finset.mem_univ t) (Matrix.diagonal_apply_ne _ ht)
  simp only [tensorOperator, hdiag, registerMatrixCLM_apply,
    register_ofMatrix_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem tensorOperator_diagonal_basis (D : Fin d → ℂ) (w : Fin n → Fin d) :
    tensorOperator n (Matrix.diagonal D) (registerBasis (Fin n → Fin d) w) =
      (∏ t, D (w t)) • registerBasis (Fin n → Fin d) w := by
  ext v
  simp only [tensorOperator_diagonal_apply, registerBasis_apply, lp.single_apply,
    Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hv : v = w <;> simp [hv]

/-- A nonzero coefficient of a Cartan-commuting operator connects only words
having exactly the same occupancy in every letter. -/
theorem cartan_commuting_coefficient_occupancy
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d))
    (hT : ∀ a, T * collectiveGenerator n a a = collectiveGenerator n a a * T)
    (v w : Fin n → Fin d)
    (hcoeff : T (registerBasis (Fin n → Fin d) v) w ≠ 0) (a : Fin d) :
    occupancy v a = occupancy w a := by
  have he := congrArg (fun Q : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) =>
    Q (registerBasis (Fin n → Fin d) v) w) (hT a)
  simp only [ContinuousLinearMap.mul_apply, collectiveGenerator_diagonal_basis,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, collectiveGenerator_diagonal] at he
  have heq : (occupancy v a : ℂ) = (occupancy w a : ℂ) := mul_right_cancel₀ hcoeff he
  exact_mod_cast heq

/-- Commutation with all actual Cartan operators implies commutation with
every literal complex diagonal tensor power, including singular diagonals. -/
theorem tensorOperator_diagonal_commutes
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d))
    (hT : ∀ a, T * collectiveGenerator n a a = collectiveGenerator n a a * T)
    (D : Fin d → ℂ) :
    T * tensorOperator n (Matrix.diagonal D) = tensorOperator n (Matrix.diagonal D) * T := by
  apply register_operator_ext
  intro w v
  rw [← registerBasis_apply]
  change T (tensorOperator n (Matrix.diagonal D) (registerBasis (Fin n → Fin d) v)) w =
    tensorOperator n (Matrix.diagonal D) (T (registerBasis (Fin n → Fin d) v)) w
  rw [tensorOperator_diagonal_basis, map_smul, tensorOperator_diagonal_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hc : T (registerBasis (Fin n → Fin d) v) w = 0
  · simp only [hc, mul_zero]
  · have hocc := cartan_commuting_coefficient_occupancy T hT v w hc
    rw [word_product_eq_occupancy D v, word_product_eq_occupancy D w]
    simp only [hocc]

end Cloning.TensorLie
