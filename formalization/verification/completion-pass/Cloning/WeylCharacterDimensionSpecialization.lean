import Cloning.WeylCharacterAlternantDenominator
import Mathlib.Algebra.Ring.GeomSum

/-!
# Principal specialization with the common vanishing factor removed

Substitution `X_i = t^i` turns the alternant into an ordinary transposed
Vandermonde. Both determinants have the same factor `(1-t)^numberOfRoots`;
that polynomial factor is cancelled before evaluating at `t=1`.
-/

noncomputable section
open scoped BigOperators Classical
open Cloning.TensorLie
namespace Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Ascending principal specialization into an actual polynomial ring. -/
def principalSpecialization (d : ℕ) : MvPolynomial (Fin d) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ Polynomial.X ^ i.val)

@[simp] theorem principalSpecialization_X (d : ℕ) (i : Fin d) :
    principalSpecialization d (MvPolynomial.X i) = Polynomial.X ^ i.val := by
  simp [principalSpecialization]

/-- The geometric quotient of `t^u-t^v` by `1-t`, for `u≤v`. -/
def powerDifferenceQuotient (u v : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ u * ∑ k ∈ Finset.range (v-u), Polynomial.X ^ k

theorem power_difference_factor {u v : ℕ} (huv : u ≤ v) :
    (Polynomial.X : Polynomial ℂ) ^ u - Polynomial.X ^ v =
      (1 - Polynomial.X) * powerDifferenceQuotient u v := by
  have hgeom := geom_sum_mul (Polynomial.X : Polynomial ℂ) (v-u)
  have hp : (Polynomial.X : Polynomial ℂ) ^ u * Polynomial.X ^ (v-u) = Polynomial.X ^ v := by
    rw [← pow_add, Nat.add_sub_of_le huv]
  unfold powerDifferenceQuotient
  linear_combination (Polynomial.X : Polynomial ℂ) ^ u * hgeom + hp

@[simp] theorem eval_one_powerDifferenceQuotient (u v : ℕ) :
    Polynomial.eval 1 (powerDifferenceQuotient u v) = ((v-u : ℕ) : ℂ) := by
  simp [powerDifferenceQuotient]

/-- The principal specialization of the alternant has no permutation sign. -/
theorem principalSpecialization_alternant {d : ℕ} (a : Fin d → ℕ) :
    principalSpecialization d (alternant a) =
      ∏ r : PositiveRoot d, ((Polynomial.X : Polynomial ℂ) ^ a r.val.2 - Polynomial.X ^ a r.val.1) := by
  rw [alternant, (principalSpecialization d).map_det]
  have hm : (principalSpecialization d).mapMatrix (fun i j : Fin d ↦ MvPolynomial.X i ^ a j) =
      (Matrix.vandermonde (fun j : Fin d ↦ (Polynomial.X : Polynomial ℂ) ^ a j)).transpose := by
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_pow, principalSpecialization_X,
      Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hm, Matrix.det_transpose, Matrix.det_vandermonde, ← prod_positiveRoot]

/-- The denominator under the same literal substitution. -/
theorem principalSpecialization_denominator (d : ℕ) :
    principalSpecialization d (denominator d) =
      ∏ r : PositiveRoot d, ((Polynomial.X : Polynomial ℂ) ^ r.val.1.val - Polynomial.X ^ r.val.2.val) := by
  simp [denominator]

/-- The factor left after removing every root's common first-order zero. -/
def alternantQuotient {d : ℕ} (a : Fin d → ℕ) : Polynomial ℂ :=
  ∏ r : PositiveRoot d, powerDifferenceQuotient (a r.val.2) (a r.val.1)

def denominatorQuotient (d : ℕ) : Polynomial ℂ :=
  ∏ r : PositiveRoot d, powerDifferenceQuotient r.val.1.val r.val.2.val

theorem principalSpecialization_alternant_factor {d : ℕ} (a : Fin d → ℕ) (ha : StrictAnti a) :
    principalSpecialization d (alternant a) =
      (1 - Polynomial.X : Polynomial ℂ) ^ Fintype.card (PositiveRoot d) * alternantQuotient a := by
  rw [principalSpecialization_alternant]
  have hfac (r : PositiveRoot d) := power_difference_factor (ha r.property).le
  simp_rw [hfac]
  simp [alternantQuotient, Finset.prod_mul_distrib]

theorem principalSpecialization_denominator_factor (d : ℕ) :
    principalSpecialization d (denominator d) =
      (1 - Polynomial.X : Polynomial ℂ) ^ Fintype.card (PositiveRoot d) * denominatorQuotient d := by
  rw [principalSpecialization_denominator]
  have hfac r := power_difference_factor (show r.val.1.val ≤ r.val.2.val from
    Nat.le_of_lt (Fin.lt_def.mp (r : PositiveRoot d).property))
  simp_rw [hfac]
  simp [denominatorQuotient, Finset.prod_mul_distrib]

@[simp] theorem eval_one_principalSpecialization {d : ℕ}
    (χ : MvPolynomial (Fin d) ℂ) :
    Polynomial.eval 1 (principalSpecialization d χ) = MvPolynomial.eval (fun _ ↦ 1) χ := by
  change Polynomial.evalRingHom 1 (MvPolynomial.eval₂Hom Polynomial.C _ χ) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X, one_pow]
  congr 2
  ext z
  simp

/-- Cancel the shared zero as a nonzero polynomial, before specialization at one. -/
theorem principalSpecialization_quotient_identity {d : ℕ}
    (χ : MvPolynomial (Fin d) ℂ) (a : Fin d → ℕ) (ha : StrictAnti a)
    (hχ : χ * denominator d = alternant a) :
    principalSpecialization d χ * denominatorQuotient d = alternantQuotient a := by
  have he := congrArg (principalSpecialization d) hχ
  rw [map_mul, principalSpecialization_denominator_factor,
    principalSpecialization_alternant_factor a ha] at he
  have hX : (1 - Polynomial.X : Polynomial ℂ) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval 0) h
    simpa using hh
  apply mul_left_cancel₀ (pow_ne_zero (Fintype.card (PositiveRoot d)) hX)
  simpa only [mul_left_comm, mul_assoc] using he

/-- The finite principal-specialization dimension formula for a strict alternant. -/
theorem eval_one_eq_root_gap_product {d : ℕ}
    (χ : MvPolynomial (Fin d) ℂ) (a : Fin d → ℕ) (ha : StrictAnti a)
    (hχ : χ * denominator d = alternant a) :
    MvPolynomial.eval (fun _ ↦ 1) χ =
      ∏ r : PositiveRoot d, (((a r.val.1 - a r.val.2 : ℕ) : ℂ) /
        ((r.val.2.val - r.val.1.val : ℕ) : ℂ)) := by
  have he := congrArg (Polynomial.eval 1)
    (principalSpecialization_quotient_identity χ a ha hχ)
  simp only [Polynomial.eval_mul, eval_one_principalSpecialization,
    denominatorQuotient, alternantQuotient, Polynomial.eval_prod,
    eval_one_powerDifferenceQuotient] at he
  rw [Finset.prod_div_distrib]
  apply (eq_div_iff ?_).mpr he
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt (Fin.lt_def.mp r.property)))

end Cloning.WeylCharacter
