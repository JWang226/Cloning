import Cloning.TensorFlatProjectorLaw
import Cloning.TensorSchurDecompositionRadialEquation

/-! The exact quadratic Casimir expectation on the physical flat tensor input. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial Cloning.YoungGeneral
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The character of the full physical tensor register is the tensor power
of the defining character, derived from its literal trace. -/
theorem tensorWeightTrace_one :
    tensorWeightTrace (1 : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) =
      (∑ a : Fin d, (X a : MvPolynomial (Fin d) ℂ))^n := by
  apply MvPolynomial.funext
  intro D
  rw [eval_tensorWeightTrace, mul_one, trace_tensorOperator_diagonal]
  simp

theorem pderiv_sum_X (a : Fin d) :
    pderiv a (∑ b : Fin d, (X b : MvPolynomial (Fin d) ℂ)) = 1 := by
  simp [pderiv_X, Pi.single_apply]

/-- The root-pair trace is computed by the exact radial commutator relation. -/
theorem tensorWeightTrace_rootPair_one (a b : Fin d) (hab : a ≠ b) :
    tensorWeightTrace (collectiveGenerator n a b * collectiveGenerator n b a) +
      tensorWeightTrace (collectiveGenerator n b a * collectiveGenerator n a b) =
    (X a + X b) * (n : MvPolynomial (Fin d) ℂ) * (∑ c, X c)^(n-1) := by
  have hne : (X a - X b : MvPolynomial (Fin d) ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hab (X_injective h)
  apply mul_left_cancel₀ hne
  have hh := tensorWeightTrace_root_pair
    (1 : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) a b (by simp)
  simp only [mul_one, one_mul, tensorWeightTrace_one, pderiv_pow, pderiv_sum_X] at hh
  rw [hh]
  ring

private theorem eval_flat_sum_X (hd : 0 < d) :
    eval (fun _ : Fin d => ((1/(d:ℝ):ℝ):ℂ)) (∑ a : Fin d, (X a : MvPolynomial (Fin d) ℂ)) = 1 := by
  simp only [map_sum, eval_X, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  simpa only [div_eq_mul_inv, one_mul] using div_self (Nat.cast_ne_zero.mpr hd.ne' : (d : ℂ) ≠ 0)

private theorem nat_mul_pred_cast (n : ℕ) :
    (n : ℂ) * ((n-1 : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ)-1) := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.cast_add]

/-- Evaluating the Cartan part at the flat spectrum gives the actual
multinomial second moment, without a probabilistic moment assumption. -/
theorem eval_flat_cartan_square (hd : 0 < d) (a : Fin d) :
    eval (fun _ : Fin d => ((1/(d:ℝ):ℝ):ℂ))
      (X a * pderiv a (X a * pderiv a ((∑ b : Fin d, X b : MvPolynomial (Fin d) ℂ)^n))) =
    (n : ℂ)/(d:ℂ) + (n:ℂ)*((n:ℂ)-1)/(d:ℂ)^2 := by
  simp only [pderiv_pow, pderiv_sum_X, mul_one, pderiv_mul]
  simp only [pderiv_X, Pi.single_apply, if_true, Derivation.map_natCast, zero_mul,
    add_zero, one_mul, mul_one, map_mul, map_add, map_pow, map_natCast, map_zero, eval_X,
    eval_flat_sum_X hd, one_pow]
  push_cast
  rw [nat_mul_pred_cast]
  ring

/-- Exact Casimir expectation on the full tensor power of I/d. -/
theorem tensor_flat_casimir_expectation (hd : 0 < d) :
    eval (fun _ : Fin d => ((1/(d:ℝ):ℝ):ℂ)) (tensorWeightTrace (collectiveCasimir n d)) =
      (n:ℂ)*(d:ℂ) + (n:ℂ)*((n:ℂ)-1)/(d:ℂ) := by
  have he := tensorWeightTrace_casimir_decomposition
    (1 : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d))
  simp only [mul_one, tensorWeightTrace_one] at he
  rw [he, map_add, map_sum]
  simp_rw [eval_flat_cartan_square hd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hroot : eval (fun _ : Fin d => ((1/(d:ℝ):ℝ):ℂ))
      (∑ a : PositiveRoot d,
        (tensorWeightTrace (collectiveGenerator n a.val.1 a.val.2 * collectiveGenerator n a.val.2 a.val.1) +
         tensorWeightTrace (collectiveGenerator n a.val.2 a.val.1 * collectiveGenerator n a.val.1 a.val.2))) =
        ((d:ℂ)-1)*(n:ℂ) := by
    have hp : (∑ a : PositiveRoot d,
        (tensorWeightTrace (collectiveGenerator n a.val.1 a.val.2 * collectiveGenerator n a.val.2 a.val.1) +
         tensorWeightTrace (collectiveGenerator n a.val.2 a.val.1 * collectiveGenerator n a.val.1 a.val.2))) =
        ∑ a : PositiveRoot d, (X a.val.1 + X a.val.2) *
          (n : MvPolynomial (Fin d) ℂ) * (∑ c, X c)^(n-1) := by
      apply Finset.sum_congr rfl
      intro a _
      exact tensorWeightTrace_rootPair_one _ _ (ne_of_lt a.property)
    rw [hp]
    simp only [map_sum, map_mul, map_add, map_natCast, map_pow, eval_X,
      eval_flat_sum_X hd, one_pow, mul_one]
    have hh := sum_positiveRoot_endpoints_complex (fun _ : Fin d => (1:ℂ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hh
    push_cast
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hd0 : (d:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    field_simp
    linear_combination (n:ℂ) * hh
  rw [hroot]
  have hd0 : (d:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  field_simp
  ring

end Cloning.TensorLie
