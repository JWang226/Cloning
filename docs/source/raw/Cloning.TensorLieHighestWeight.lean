import Cloning.TensorLieRelations

/-! A concrete normalized highest-weight tensor for the one-row partition.
The general Schur-sector construction is separate from this elementary case. -/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

theorem slotGenerator_constant_basis_zero (t : Fin n) (a b c : A) (hbc : b ≠ c) :
    slotGenerator t a b (registerBasis (Fin n → A) (fun _ => c)) = 0 := by
  ext w
  have hn : Function.update w t b ≠ (fun _ => c) := by
    intro he
    have h := congrFun he t
    exact hbc (by simpa using h)
  simp [slotGenerator_apply, registerBasis_apply, lp.single_apply, hn]

theorem collectiveGenerator_constant_basis_zero (a b c : A) (hbc : b ≠ c) :
    collectiveGenerator n a b (registerBasis (Fin n → A) (fun _ => c)) = 0 := by
  simp only [collectiveGenerator, ContinuousLinearMap.sum_apply,
    slotGenerator_constant_basis_zero _ a b c hbc, Finset.sum_const_zero]

omit [Fintype A] in
theorem occupancy_constant (a c : A) :
    occupancy (fun _ : Fin n => c) a = if c = a then n else 0 := by
  by_cases h : c = a <;> simp [occupancy, h]

def highestTensor (n d : ℕ) : TensorRegister n (Fin (d + 1)) :=
  registerBasis (Fin n → Fin (d + 1)) (fun _ => 0)

theorem highestTensor_norm (n d : ℕ) : ‖highestTensor n d‖ = 1 :=
  (registerBasis (Fin n → Fin (d + 1))).orthonormal.norm_eq_one _

/-- Every actual raising generator annihilates the constant-zero tensor. -/
theorem highestTensor_raising_zero (n d : ℕ) (a b : Fin (d + 1)) (hab : a < b) :
    collectiveGenerator n a b (highestTensor n d) = 0 := by
  apply collectiveGenerator_constant_basis_zero
  intro hb
  subst b
  exact (not_lt_of_ge (Fin.zero_le a)) hab

/-- Its Cartan weight is precisely the one-row partition `(n,0,…,0)`. -/
theorem highestTensor_cartan (n d : ℕ) (a : Fin (d + 1)) :
    collectiveGenerator n a a (highestTensor n d) =
      (if a = 0 then (n : ℂ) else 0) • highestTensor n d := by
  rw [highestTensor, collectiveGenerator_diagonal_basis, occupancy_constant]
  by_cases ha : a = 0 <;> simp [ha, eq_comm]

end Cloning.TensorLie
