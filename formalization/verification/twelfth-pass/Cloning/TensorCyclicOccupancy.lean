import Cloning.TensorCyclicFiltration

/-! Actual occupation support and Cartan defects on cyclic lowering cutoffs. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem occupancy_update (w : Fin n → Fin d) (t : Fin n) (a i : Fin d) :
    occupancy (Function.update w t a) i + (if w t = i then 1 else 0) =
      occupancy w i + (if a = i then 1 else 0) := by
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun u _ => show
      (if Function.update w t a u = i then 1 else 0) +
        (if u = t then (if w t = i then 1 else 0) else 0) =
      (if w u = i then 1 else 0) +
        (if u = t then (if a = i then 1 else 0) else 0) from by
      by_cases h : u = t
      · subst u; simp [Nat.add_comm]
      · simp [h])
  simpa only [occupancy, Finset.card_filter, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using he

theorem occupancy_update_dist_le_one (w : Fin n → Fin d) (t : Fin n) (a i : Fin d) :
    |(occupancy (Function.update w t a) i : ℤ) - occupancy w i| ≤ 1 := by
  have he := occupancy_update w t a i
  rw [abs_le]
  split_ifs at he <;> omega

/-- A lowering word can move any individual occupation by at most its total
positive-root height. This statement is about literal computational coefficients. -/
theorem loweringWord_occupancy_bound
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : List (PositiveRoot d)) (v : Fin n → Fin d)
    (hv : loweringWord Ω w v ≠ 0) (i : Fin d) :
    |(occupancy v i : ℤ) - mu i| ≤ loweringHeight w := by
  induction w generalizing v with
  | nil =>
      have he := congrArg (fun x : TensorRegister n (Fin d) => x v) (hweight i)
      simp only [collectiveGenerator_diagonal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
      have heq : (occupancy v i : ℂ) = (mu i : ℂ) := (mul_right_cancel₀ hv he)
      have hnat : occupancy v i = mu i := by exact_mod_cast heq
      simp [hnat, loweringHeight]
  | cons a w ih =>
      have hv' : (∑ t : Fin n, if v t = a.val.2 then
          loweringWord Ω w (Function.update v t a.val.1) else 0) ≠ 0 := by
        simpa only [loweringWord, collectiveGenerator_apply] using hv
      obtain ⟨t, ht⟩ : ∃ t : Fin n, (if v t = a.val.2 then
          loweringWord Ω w (Function.update v t a.val.1) else 0) ≠ 0 := by
        by_contra! hn
        exact hv' (Finset.sum_eq_zero (fun t _ => hn t))
      have ht' : loweringWord Ω w (Function.update v t a.val.1) ≠ 0 := by
        split_ifs at ht with htval
        · exact ht
        · exact False.elim (ht rfl)
      have hi := ih _ ht'
      have hd := occupancy_update_dist_le_one v t a.val.1 i
      have ha := a.height_pos
      rw [abs_le] at hi hd ⊢
      simp only [loweringHeight, Nat.cast_add]
      omega

def occupancyBand (mu : Fin d → ℕ) (r : ℕ) : Submodule ℂ (TensorRegister n (Fin d)) where
  carrier := {x | ∀ w i, (r : ℤ) < |(occupancy w i : ℤ) - mu i| → x w = 0}
  zero_mem' := by intro w i _; rfl
  add_mem' := by intro x y hx hy w i hi; simp [hx w i hi, hy w i hi]
  smul_mem' := by intro c x hx w i hi; simp [lp.coeFn_smul, hx w i hi]

theorem cyclicCutoff_le_occupancyBand
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) (r : ℕ) :
    cyclicCutoff Ω r ≤ occupancyBand mu r := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, rfl⟩ v i hi
  by_contra hv
  have hh := loweringWord_occupancy_bound Ω mu hweight w v hv i
  omega

theorem cyclicCutoff_occupancy_bound
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r)
    (v : Fin n → Fin d) (hv : x v ≠ 0) (i : Fin d) :
    |(occupancy v i : ℤ) - mu i| ≤ r := by
  by_contra! h
  exact hv (cyclicCutoff_le_occupancyBand Ω mu hweight r hx v i h)

theorem register_norm_sq_eq_sum {A : Type*} [Fintype A] (x : Register A) :
    ‖x‖ ^ 2 = ∑ a, ‖x a‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype] using
    (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x)

theorem register_norm_le_of_pointwise {A : Type*} [Fintype A] (x y : Register A)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ a, ‖x a‖ ≤ C * ‖y a‖) : ‖x‖ ≤ C * ‖y‖ := by
  have hh : ‖x‖ ^ 2 ≤ C ^ 2 * ‖y‖ ^ 2 := by
    rw [register_norm_sq_eq_sum, register_norm_sq_eq_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    nlinarith [h a, norm_nonneg (x a), norm_nonneg (y a)]
  nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg hC (norm_nonneg y)]

/-- The exact Cartan occupation operator differs from its highest weight by
at most the root-height cutoff. -/
theorem cartan_defect_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) (i : Fin d) :
    ‖collectiveGenerator n i i x - (mu i : ℂ) • x‖ ≤ (r : ℝ) * ‖x‖ := by
  apply register_norm_le_of_pointwise _ x r (Nat.cast_nonneg r)
  intro v
  simp only [lp.coeFn_sub, Pi.sub_apply, collectiveGenerator_diagonal,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← sub_mul, norm_mul]
  by_cases hv : x v = 0
  · simp [hv]
  · have hb := cyclicCutoff_occupancy_bound Ω mu hweight r hx v hv i
    have hb' : |(occupancy v i : ℝ) - mu i| ≤ (r : ℝ) := by exact_mod_cast hb
    have hc : ‖(occupancy v i : ℂ) - mu i‖ ≤ (r : ℝ) := by
      simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hb'
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem cartan_difference_defect_norm_le
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (r : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) (a b : Fin d) :
    ‖collectiveGenerator n a a x - collectiveGenerator n b b x -
      ((mu a : ℂ) - mu b) • x‖ ≤ (2 * r : ℝ) * ‖x‖ := by
  have he : collectiveGenerator n a a x - collectiveGenerator n b b x -
      ((mu a : ℂ) - mu b) • x =
      (collectiveGenerator n a a x - (mu a : ℂ) • x) -
      (collectiveGenerator n b b x - (mu b : ℂ) • x) := by module
  rw [he]
  calc
    _ ≤ ‖collectiveGenerator n a a x - (mu a : ℂ) • x‖ +
        ‖collectiveGenerator n b b x - (mu b : ℂ) • x‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) * ‖x‖ + r * ‖x‖ := add_le_add
      (cartan_defect_norm_le Ω mu hweight r hx a)
      (cartan_defect_norm_le Ω mu hweight r hx b)
    _ = _ := by ring

end Cloning.TensorLie
