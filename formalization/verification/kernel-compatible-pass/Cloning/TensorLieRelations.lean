import Cloning.TensorLieGenerators

/-! Exact collective Lie relations and Cartan occupancy on physical tensors. -/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

theorem slot_collective_commutator (t : Fin n) (a b c e : A) :
    slotGenerator t a b * collectiveGenerator n c e -
      collectiveGenerator n c e * slotGenerator t a b =
        (if b = c then slotGenerator t a e else 0) -
          (if e = a then slotGenerator t c b else 0) := by
  calc
    _ = ∑ u : Fin n, (slotGenerator t a b * slotGenerator u c e -
        slotGenerator u c e * slotGenerator t a b) := by
      simp only [collectiveGenerator, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    _ = slotGenerator t a b * slotGenerator t c e -
        slotGenerator t c e * slotGenerator t a b := by
      apply Finset.sum_eq_single t
      · intro u _ hut
        exact sub_eq_zero.mpr (slotGenerator_commute hut.symm a b c e).eq
      · simp
    _ = _ := by rw [slotGenerator_mul_same, slotGenerator_mul_same]

/-- The literal tensor generators satisfy the `gl(A)` commutator exactly. -/
theorem collectiveGenerator_commutator (a b c e : A) :
    collectiveGenerator n a b * collectiveGenerator n c e -
      collectiveGenerator n c e * collectiveGenerator n a b =
        (if b = c then collectiveGenerator n a e else 0) -
          (if e = a then collectiveGenerator n c b else 0) := by
  calc
    _ = ∑ t : Fin n, (slotGenerator t a b * collectiveGenerator n c e -
        collectiveGenerator n c e * slotGenerator t a b) := by
      conv_lhs => arg 1; arg 1; unfold collectiveGenerator
      conv_lhs => arg 2; arg 2; unfold collectiveGenerator
      simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by
      simp_rw [slot_collective_commutator, Finset.sum_sub_distrib]
      by_cases hbc : b = c <;> by_cases hea : e = a <;>
        simp only [hbc, hea, ite_true, ite_false, Finset.sum_const_zero, collectiveGenerator]

def occupancy (w : Fin n → A) (a : A) : ℕ :=
  (Finset.univ.filter (fun t => w t = a)).card

/-- Cartan generators are the actual diagonal occupation-number operators. -/
theorem collectiveGenerator_diagonal (a : A) (x : TensorRegister n A) (w : Fin n → A) :
    collectiveGenerator n a a x w = (occupancy w a : ℂ) * x w := by
  rw [collectiveGenerator_apply]
  calc
    _ = ∑ t : Fin n, if w t = a then x w else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : w t = a
      · simp only [if_pos ht]
        rw [← ht, Function.update_eq_self]
      · simp [ht]
    _ = _ := by simp [occupancy, ← Finset.sum_filter, nsmul_eq_mul]

theorem collectiveGenerator_diagonal_basis (a : A) (w : Fin n → A) :
    collectiveGenerator n a a (registerBasis (Fin n → A) w) =
      (occupancy w a : ℂ) • registerBasis (Fin n → A) w := by
  ext v
  simp only [collectiveGenerator_diagonal, registerBasis_apply, lp.single_apply,
    Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : v = w <;> simp [h]

theorem sum_occupancy (w : Fin n → A) : ∑ a : A, occupancy w a = n := by
  simp only [occupancy, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_collectiveGenerator_diagonal :
    (∑ a : A, collectiveGenerator n a a) =
      (n : ℂ) • ContinuousLinearMap.id ℂ (TensorRegister n A) := by
  ext x w
  simp only [ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply,
    collectiveGenerator_diagonal, ← Finset.sum_mul, ← Nat.cast_sum, sum_occupancy,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]

end Cloning.TensorLie
