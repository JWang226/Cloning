import Cloning.TensorLieHighestWeight

/-! Actual simple-root-height support cutoffs on finite tensor registers.
These supply concrete raising and lowering invariants for the one-row
highest-weight tensor; no filtration-shift assumptions are used. -/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def wordHeight (w : Fin n → Fin (d + 1)) : ℕ := ∑ t, (w t).val

theorem wordHeight_update (w : Fin n → Fin (d + 1)) (t : Fin n) (a : Fin (d + 1)) :
    wordHeight (Function.update w t a) + (w t).val = wordHeight w + a.val := by
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun u _ => show (Function.update w t a u).val + (if u = t then (w t).val else 0) =
      (w u).val + (if u = t then a.val else 0) from by
        by_cases h : u = t
        · subst u; simp [Nat.add_comm]
        · simp [h])
  simpa only [wordHeight, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using he

def heightCutoff (n d r : ℕ) : Submodule ℂ (TensorRegister n (Fin (d + 1))) where
  carrier := {x | ∀ w, r < wordHeight w → x w = 0}
  zero_mem' := by intro w _; rfl
  add_mem' := by intro x y hx hy w hw; simp [hx w hw, hy w hw]
  smul_mem' := by intro c x hx w hw; simp [lp.coeFn_smul, hx w hw]

theorem heightCutoff_monotone (n d : ℕ) : Monotone (heightCutoff n d) := by
  intro r s hrs x hx w hw
  exact hx w (hrs.trans_lt hw)

theorem highestTensor_mem_heightCutoff_zero (n d : ℕ) :
    highestTensor n d ∈ heightCutoff n d 0 := by
  intro w hw
  have hn : w ≠ (fun _ => 0) := by
    intro he
    rw [he] at hw
    simp [wordHeight] at hw
  simp [highestTensor, registerBasis_apply, lp.single_apply, hn]

/-- A raising root lowers the actual height cutoff by at least one. -/
theorem collectiveGenerator_lowers_cutoff (a b : Fin (d + 1)) (hab : a < b)
    (r : ℕ) (x : TensorRegister n (Fin (d + 1))) (hx : x ∈ heightCutoff n d (r + 1)) :
    collectiveGenerator n a b x ∈ heightCutoff n d r := by
  intro w hw
  rw [collectiveGenerator_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ha : w t = a
  · rw [if_pos ha]
    apply hx
    have hh := wordHeight_update w t b
    rw [ha] at hh
    have : a.val < b.val := hab
    omega
  · rw [if_neg ha]

theorem collectiveGenerator_zero_cutoff (a b : Fin (d + 1)) (hab : a < b)
    (x : TensorRegister n (Fin (d + 1))) (hx : x ∈ heightCutoff n d 0) :
    collectiveGenerator n a b x = 0 := by
  ext w
  rw [collectiveGenerator_apply]
  change _ = 0
  apply Finset.sum_eq_zero
  intro t _
  by_cases ha : w t = a
  · rw [if_pos ha]
    apply hx
    have hh := wordHeight_update w t b
    rw [ha] at hh
    have : a.val < b.val := hab
    omega
  · rw [if_neg ha]

/-- A lowering root raises simple-root height by at most `d`. -/
theorem collectiveGenerator_raises_cutoff (a b : Fin (d + 1))
    (r : ℕ) (x : TensorRegister n (Fin (d + 1))) (hx : x ∈ heightCutoff n d r) :
    collectiveGenerator n b a x ∈ heightCutoff n d (r + d) := by
  intro w hw
  rw [collectiveGenerator_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases hb : w t = b
  · rw [if_pos hb]
    apply hx
    have hh := wordHeight_update w t a
    rw [hb] at hh
    have := b.isLt
    omega
  · rw [if_neg hb]

end Cloning.TensorLie
