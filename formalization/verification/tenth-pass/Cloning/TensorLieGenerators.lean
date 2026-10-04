import Cloning.PCTTensorFrame
import Cloning.InfiniteFiniteCorner

/-!
# Literal matrix-unit generators on finite tensor registers

Each one-slot generator changes the letter in that slot. The construction is
an actual bounded operator on the computational-word Hilbert space, rather
than an abstract representation satisfying postulated Lie relations.
-/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteFiniteCorner
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

abbrev TensorRegister (n : ℕ) (A : Type*) := Register (Fin n → A)

def slotMatrix (t : Fin n) (a b : A) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  fun w v => if w t = a ∧ v = Function.update w t b then 1 else 0

def slotGenerator (t : Fin n) (a b : A) : TensorRegister n A →L[ℂ] TensorRegister n A :=
  ofMatrix (registerBasis (Fin n → A)) (slotMatrix t a b)

/-- The operator acts by the literal tensor matrix-unit formula. -/
@[simp] theorem slotGenerator_apply (t : Fin n) (a b : A)
    (x : TensorRegister n A) (w : Fin n → A) :
    slotGenerator t a b x w = if w t = a then x (Function.update w t b) else 0 := by
  rw [← register_inner_single, ← registerBasis_apply]
  rw [slotGenerator, inner_ofMatrix_apply (registerBasis _).orthonormal]
  simp only [registerBasis_apply, register_inner_single]
  by_cases h : w t = a <;> simp [slotMatrix, h]

omit [Fintype A] [DecidableEq A] in
theorem update_relation (t : Fin n) (a b : A) (w v : Fin n → A) :
    (w t = a ∧ v = Function.update w t b) ↔
      (v t = b ∧ w = Function.update v t a) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [Function.update_idem, ← h, Function.update_eq_self]
  · rintro ⟨h, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [Function.update_idem, ← h, Function.update_eq_self]

omit [Fintype A] in
theorem slotMatrix_adjoint (t : Fin n) (a b : A) :
    (slotMatrix t a b)ᴴ = slotMatrix t b a := by
  ext w v
  have he := update_relation t a b v w
  by_cases h : v t = a ∧ w = Function.update v t b
  · simp only [Matrix.conjTranspose_apply, slotMatrix, if_pos h, if_pos (he.mp h), star_one]
  · have h' : ¬(w t = b ∧ v = Function.update w t a) := fun hh => h (he.mpr hh)
    simp only [Matrix.conjTranspose_apply, slotMatrix, if_neg h, if_neg h', star_zero]

theorem slotGenerator_adjoint (t : Fin n) (a b : A) :
    (slotGenerator t a b).adjoint = slotGenerator t b a := by
  rw [← ContinuousLinearMap.star_eq_adjoint, slotGenerator,
    ← ofMatrix_conjTranspose, slotMatrix_adjoint]
  rfl

theorem slotGenerator_mul_same (t : Fin n) (a b c e : A) :
    slotGenerator t a b * slotGenerator t c e =
      if b = c then slotGenerator t a e else 0 := by
  ext x w
  simp only [ContinuousLinearMap.mul_apply, slotGenerator_apply,
    Function.update_self, Function.update_idem]
  by_cases hbc : b = c <;> by_cases hwa : w t = a <;> simp [hbc, hwa]

theorem slotGenerator_commute {t u : Fin n} (htu : t ≠ u) (a b c e : A) :
    Commute (slotGenerator t a b) (slotGenerator u c e) := by
  apply ContinuousLinearMap.ext
  intro x
  ext w
  simp only [ContinuousLinearMap.mul_apply, slotGenerator_apply,
    Function.update_of_ne htu, Function.update_of_ne htu.symm]
  rw [Function.update_comm htu]
  by_cases hwa : w t = a <;> by_cases hwc : w u = c <;> simp [hwa, hwc]

theorem slotGenerator_norm_le_one (t : Fin n) (a b : A) :
    ‖slotGenerator t a b‖ ≤ 1 := by
  have hp := CStarRing.norm_star_mul_self (x := slotGenerator t b b)
  simp only [ContinuousLinearMap.star_eq_adjoint, slotGenerator_adjoint,
    slotGenerator_mul_same, if_true] at hp
  have hpbound : ‖slotGenerator t b b‖ ≤ 1 := by
    have := norm_nonneg (slotGenerator t b b)
    nlinarith
  have he := CStarRing.norm_star_mul_self (x := slotGenerator t a b)
  simp only [ContinuousLinearMap.star_eq_adjoint, slotGenerator_adjoint,
    slotGenerator_mul_same, if_true] at he
  have := norm_nonneg (slotGenerator t a b)
  nlinarith

def collectiveGenerator (n : ℕ) (a b : A) :
    TensorRegister n A →L[ℂ] TensorRegister n A := ∑ t : Fin n, slotGenerator t a b

@[simp] theorem collectiveGenerator_apply (a b : A)
    (x : TensorRegister n A) (w : Fin n → A) :
    collectiveGenerator n a b x w =
      ∑ t : Fin n, if w t = a then x (Function.update w t b) else 0 := by
  simp only [collectiveGenerator, ContinuousLinearMap.sum_apply, lp.coeFn_sum,
    Finset.sum_apply, slotGenerator_apply]

theorem collectiveGenerator_adjoint (a b : A) :
    (collectiveGenerator n a b).adjoint = collectiveGenerator n b a := by
  simp only [collectiveGenerator, map_sum, slotGenerator_adjoint]

theorem collectiveGenerator_norm_le (a b : A) :
    ‖collectiveGenerator n a b‖ ≤ n := by
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
    slotGenerator_norm_le_one t a b)
  simpa using h

end Cloning.TensorLie
