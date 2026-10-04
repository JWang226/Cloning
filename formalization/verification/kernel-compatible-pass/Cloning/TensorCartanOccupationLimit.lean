import Cloning.TensorCartanMatrixLimit
import Cloning.TensorCartanSplitMultiplicity
import Cloning.Occupation

/-! Grouping the literal physical Cartan word assignments by root occupations. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

local instance : DecidableEq (PositiveRoot d → ℕ) := Classical.decEq _

private theorem list_count_decide {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α]
    (a : α) (l : List α) : l.count a = l.countP (fun b => decide (b = a)) := by
  unfold List.count
  congr 1
  funext b
  exact Bool.beq_eq_decide_eq b a

theorem wordAmplitude_perm (t : PositiveRoot d → ℝ) {u v : List (PositiveRoot d)}
    (h : u.Perm v) : wordAmplitude t u = wordAmplitude t v :=
  (h.map (fun a => Real.sqrt (t a))).prod_eq

theorem splitFactorialCoefficient_perm (w : List (PositiveRoot d))
    {u u' v v' : List (PositiveRoot d)} (hu : u.Perm u') (hv : v.Perm v') :
    splitFactorialCoefficient w u v = splitFactorialCoefficient w u' v' := by
  simp only [splitFactorialCoefficient, PBW.occupationFactorial_eq_of_perm hu,
    PBW.occupationFactorial_eq_of_perm hv]

private theorem list_sum_indicator {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → β) (k : β) (c : ℂ) :
    (l.map (fun a => if f a = k then c else 0)).sum = ((l.map f).count k : ℂ) * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : f a = k
    · simp [h, ih, List.count_cons, add_mul, add_comm]
    · simp [h, Ne.symm h, ih, List.count_cons]

/-- Compatible output occupations collect the assignment sum into the exact
product of binomial multiplicities times its common normalized coefficient. -/
theorem occupationSplitMatrixElement_eq_choices
    (t : PositiveRoot d → ℝ) (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    occupationSplitMatrixElement t w u v =
      (occupationChoices w (fun a => u.count a) : ℂ) *
        (splitFactorialCoefficient w u v * (wordAmplitude t u : ℂ) *
          (wordAmplitude (fun a => 1 - t a) v : ℂ)) := by
  classical
  unfold occupationSplitMatrixElement
  have he : (loweringSplits w).map (fun ab =>
      (splitFactorialCoefficient w ab.1 ab.2 * (wordAmplitude t ab.1 : ℂ) *
        (wordAmplitude (fun a => 1 - t a) ab.2 : ℂ)) *
        ((if u.Perm ab.1 then 1 else 0 : ℂ) * (if v.Perm ab.2 then 1 else 0 : ℂ))) =
      (loweringSplits w).map (fun ab =>
        if (fun a => ab.1.count a) = (fun a => u.count a) then
          splitFactorialCoefficient w u v * (wordAmplitude t u : ℂ) *
            (wordAmplitude (fun a => 1 - t a) v : ℂ) else 0) := by
    apply List.map_congr_left
    intro ab hab
    by_cases hu : u.Perm ab.1
    · have hv : v.Perm ab.2 := by
        apply List.perm_iff_count.mpr
        intro a
        have hsplit := (loweringSplits_grading w ab.1 ab.2 hab).2.2 a
        have hu' := hu.count_eq a
        have hc := hcount a
        omega
      have hc : (fun a => ab.1.count a) = (fun a => u.count a) :=
        funext (fun a => (hu.count_eq a).symm)
      simp only [if_pos hu, if_pos hv, if_pos hc, mul_one,
        ← splitFactorialCoefficient_perm w hu hv,
        ← wordAmplitude_perm t hu, ← wordAmplitude_perm (fun a => 1 - t a) hv]
    · have hc : (fun a => ab.1.count a) ≠ (fun a => u.count a) := by
        intro hc
        apply hu
        apply List.perm_iff_count.mpr
        intro a
        exact (congrFun hc a).symm
      simp only [if_neg hu, if_neg hc, zero_mul, mul_zero]
  rw [he, list_sum_indicator, loweringSplits_count_left_occupations]
  rfl

/-- Incompatible root occupations have exactly zero limiting matrix element. -/
theorem occupationSplitMatrixElement_eq_zero
    (t : PositiveRoot d → ℝ) (w u v : List (PositiveRoot d))
    (hcount : ¬ ∀ a, u.count a + v.count a = w.count a) :
    occupationSplitMatrixElement t w u v = 0 := by
  unfold occupationSplitMatrixElement
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hz
  by_cases hu : u.Perm ab.1
  · by_cases hv : v.Perm ab.2
    · exfalso
      apply hcount
      intro a
      rw [hu.count_eq a, hv.count_eq a]
      exact (loweringSplits_grading w ab.1 ab.2 hab).2.2 a
    · simp [hv]
  · simp [hu]

/-- The binomial multiplicities exactly cancel the occupation factorials. -/
theorem occupationChoices_mul_factorials
    (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    occupationChoices w (fun a => u.count a) * PBW.occupationFactorial u *
      PBW.occupationFactorial v = PBW.occupationFactorial w := by
  simp only [occupationChoices, PBW.occupationFactorial_eq_prod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  have hc : u.count a ≤ w.count a := by have := hcount a; omega
  have hv : w.count a - u.count a = v.count a := by have := hcount a; omega
  have hh := Nat.choose_mul_factorial_mul_factorial hc
  rw [hv] at hh
  simpa only [list_count_decide] using hh

theorem occupationChoices_pos
    (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    0 < occupationChoices w (fun a => u.count a) := by
  unfold occupationChoices
  apply Finset.prod_pos
  intro a _
  change 0 < (w.count a).choose (u.count a)
  exact Nat.choose_pos (by have := hcount a; omega)

theorem occupationChoices_mul_splitFactorialCoefficient
    (w u v : List (PositiveRoot d))
    (hcount : ∀ a, u.count a + v.count a = w.count a) :
    (occupationChoices w (fun a => u.count a) : ℂ) * splitFactorialCoefficient w u v =
      (Real.sqrt (occupationChoices w (fun a => u.count a) : ℝ) : ℂ) := by
  let C := occupationChoices w (fun a => u.count a)
  have hC : 0 < (C : ℝ) := by exact_mod_cast occupationChoices_pos w u v hcount
  have hF (s : List (PositiveRoot d)) : 0 < (PBW.occupationFactorial s : ℝ) := by
    exact_mod_cast PBW.occupationFactorial_pos s
  have hid : (PBW.occupationFactorial w : ℝ) =
      (C : ℝ) * PBW.occupationFactorial u * PBW.occupationFactorial v := by
    exact_mod_cast (occupationChoices_mul_factorials w u v hcount).symm
  have he : (C : ℝ) * (Real.sqrt (PBW.occupationFactorial u : ℝ) *
      Real.sqrt (PBW.occupationFactorial v : ℝ) / Real.sqrt (PBW.occupationFactorial w : ℝ)) =
      Real.sqrt (C : ℝ) := by
    rw [hid, Real.sqrt_mul (mul_nonneg hC.le (hF u).le), Real.sqrt_mul hC.le]
    have hc0 := (Real.sqrt_pos.mpr hC).ne'
    have hu0 := (Real.sqrt_pos.mpr (hF u)).ne'
    have hv0 := (Real.sqrt_pos.mpr (hF v)).ne'
    field_simp
    nlinarith [Real.sq_sqrt hC.le]
  unfold splitFactorialCoefficient
  exact_mod_cast he

end Cloning.TensorLie
