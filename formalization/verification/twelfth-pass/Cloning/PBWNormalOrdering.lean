import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# Quantitative finite-word PBW normal ordering

This file isolates the normal-ordering argument in the fixed-height PBW proof.
It works for any collection of lowering operators and their adjoints, with no
restriction on rank. The input is a bound on transported commutator defects,
not a bound on Gram matrices. The output is an explicit finite-word Gram bound
against the bosonic Wick contraction coefficient. No highest-weight module is
postulated or constructed here: its local root-operator estimates are the
separate input needed to instantiate this general theorem.
-/

noncomputable section
open scoped InnerProductSpace
set_option linter.unusedSectionVars false
namespace Cloning.PBW

variable {ι H : Type*} [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Ordered operator word, with the leftmost operator acting last. -/
def word (F : ι → H →L[ℂ] H) : List ι → H → H
  | [], x => x
  | i :: w, x => F i (word F w x)

@[simp] theorem word_nil (F : ι → H →L[ℂ] H) (x : H) : word F [] x = x := rfl
@[simp] theorem word_cons (F : ι → H →L[ℂ] H) (i : ι) (w : List ι) (x : H) :
    word F (i :: w) x = F i (word F w x) := rfl

/-- One deletion for every occurrence of `i`; multiplicities are retained. -/
def removeOne (i : ι) : List ι → List (List ι)
  | [] => []
  | j :: w => (if i = j then [w] else []) ++ (removeOne i w).map (List.cons j)

@[simp] theorem removeOne_nil (i : ι) : removeOne i [] = [] := rfl

theorem removeOne_length_le (i : ι) (w : List ι) :
    (removeOne i w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons j w ih =>
      simp only [removeOne, List.length_append, List.length_map, List.length_cons]
      split_ifs <;> simp_all only [List.length_singleton, List.length_nil] <;> omega

theorem length_of_mem_removeOne (i : ι) (w t : List ι) (ht : t ∈ removeOne i w) :
    t.length + 1 = w.length := by
  induction w generalizing t with
  | nil => simp at ht
  | cons j w ih =>
      simp only [removeOne, List.mem_append, List.mem_map] at ht
      rcases ht with ht | ⟨s, hs, rfl⟩
      · split_ifs at ht with hij
        · have htw : t = w := by simpa using ht
          subst t
          rfl
        · simp at ht
      · simp only [List.length_cons]
        have := ih s hs
        omega

/-- Bosonic vacuum contraction number, computable recursively for any two words.
It counts bijections matching equal root labels. -/
def wick : List ι → List ι → ℕ
  | [], v => if v = [] then 1 else 0
  | i :: u, v => ((removeOne i v).map (wick u)).sum

@[simp] theorem wick_nil_nil : wick ([] : List ι) [] = 1 := by simp [wick]
@[simp] theorem wick_nil_cons (i : ι) (v : List ι) : wick [] (i :: v) = 0 := by
  simp [wick]
@[simp] theorem wick_cons_nil (i : ι) (u : List ι) : wick (i :: u) [] = 0 := by
  simp [wick]

/-- The normalized canonical commutator defect, applied to a vector. -/
def commutatorDefect (F A : ι → H →L[ℂ] H) (i j : ι) (x : H) : H :=
  A i (F j x) - F j (A i x) - if i = j then x else 0

/-- Terms produced by commuting one annihilator through a creation word.
Each term is one commutator defect with the preceding creators applied. -/
def errorTerms (F A : ι → H →L[ℂ] H) (Ω : H) (i : ι) : List ι → List H
  | [] => []
  | j :: w => commutatorDefect F A i j (word F w Ω) ::
      (errorTerms F A Ω i w).map (F j)

@[simp] theorem errorTerms_length (F A : ι → H →L[ℂ] H) (Ω : H) (i : ι)
    (w : List ι) : (errorTerms F A Ω i w).length = w.length := by
  induction w with
  | nil => rfl
  | cons j w ih => simp [errorTerms, ih]

private theorem map_sum_clm (T : H →L[ℂ] H) (l : List H) :
    T l.sum = (l.map T).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem inner_list_sum (x : H) (l : List H) :
    ⟪x, l.sum⟫_ℂ = (l.map (fun y => ⟪x, y⟫_ℂ)).sum := by
  induction l with
  | nil => simp
  | cons y l ih => simp [inner_add_right, ih]

/-- Exact normal ordering, with every commutator error retained explicitly. -/
theorem annihilator_word (F A : ι → H →L[ℂ] H) (Ω : H)
    (hΩ : ∀ i, A i Ω = 0) (i : ι) (w : List ι) :
    A i (word F w Ω) =
      ((removeOne i w).map (fun t => word F t Ω)).sum +
        (errorTerms F A Ω i w).sum := by
  induction w with
  | nil => simp [word, removeOne, errorTerms, hΩ]
  | cons j w ih =>
      simp only [word_cons, removeOne, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, errorTerms, List.sum_cons]
      have hm :
          ((removeOne i w).map (fun t => F j (word F t Ω))).sum =
            F j (((removeOne i w).map (fun t => word F t Ω)).sum) := by
        rw [map_sum_clm, List.map_map]
        rfl
      rw [hm, ← map_sum_clm]
      unfold commutatorDefect
      rw [ih, map_add]
      split_ifs <;> simp only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, zero_add] <;> abel

private theorem norm_list_sum_le (l : List H) (ε : ℝ) (_hε : 0 ≤ ε)
    (hl : ∀ x ∈ l, ‖x‖ ≤ ε) : ‖l.sum‖ ≤ l.length * ε := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx := hl x (by simp)
      have ht := ih (fun y hy => hl y (by simp [hy]))
      simpa [Nat.cast_add, Nat.cast_one, add_mul, add_comm] using (norm_add_le x l.sum).trans
        (add_le_add hx ht)

/-- Quantitative normal ordering from bounds on transported commutators. -/
theorem annihilator_word_error_le (F A : ι → H →L[ℂ] H) (Ω : H)
    (hΩ : ∀ i, A i Ω = 0) (i : ι) (w : List ι) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ x ∈ errorTerms F A Ω i w, ‖x‖ ≤ ε) :
    ‖A i (word F w Ω) -
      ((removeOne i w).map (fun t => word F t Ω)).sum‖ ≤ w.length * ε := by
  rw [annihilator_word F A Ω hΩ, add_sub_cancel_left]
  simpa using norm_list_sum_le (errorTerms F A Ω i w) ε hε herr

/-- An explicit rank-independent constant for a right word of length at most `L`.
The recurrence gives `L + L² + ⋯ + L^k`. -/
def gramConstant (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => L * (gramConstant L k + 1)

private theorem complex_list_sum_bound (l : List ι) (f g : ι → ℂ) (C : ℝ)
    (_hC : 0 ≤ C) (h : ∀ t ∈ l, ‖f t - g t‖ ≤ C) :
    ‖(l.map f).sum - (l.map g).sum‖ ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons t l ih =>
      have ht := h t (by simp)
      have hl := ih (fun s hs => h s (by simp [hs]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [show f t + (l.map f).sum - (g t + (l.map g).sum) =
        (f t - g t) + ((l.map f).sum - (l.map g).sum) by ring]
      simpa [Nat.cast_add, Nat.cast_one, add_mul, add_comm] using
        (norm_add_le _ _).trans (add_le_add ht hl)

/-- Fixed-word Gram estimate derived from annihilation of the vacuum, adjointness,
bounded generated vectors, and small transported commutator defects.

Only finitely many words, of length at most `L`, occur in the assumptions.
Consequently local cutoff operator bounds suffice; a uniform global bound on
creation operators is neither required nor asserted. -/
theorem gram_error_le (F A : ι → H →L[ℂ] H) (Ω : H) (L : ℕ)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hnorm : ⟪Ω, Ω⟫_ℂ = 1) (hΩ : ∀ i, A i Ω = 0)
    (hadj : ∀ i x y, ⟪F i x, y⟫_ℂ = ⟪x, A i y⟫_ℂ)
    (hword : ∀ u : List ι, u.length ≤ L → ‖word F u Ω‖ ≤ B)
    (herr : ∀ i w, w.length ≤ L →
      ∀ x ∈ errorTerms F A Ω i w, ‖x‖ ≤ ε)
    (u v : List ι) (hu : u.length ≤ L) (hv : v.length ≤ L) :
    ‖⟪word F u Ω, word F v Ω⟫_ℂ - (wick u v : ℂ)‖ ≤
      (gramConstant L u.length : ℝ) * B * ε := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => simp only [word_nil, wick_nil_nil, hnorm, Nat.cast_one, sub_self, norm_zero,
          List.length_nil, gramConstant, Nat.cast_zero, zero_mul, le_refl]
      | cons j v =>
          have hz : ⟪Ω, F j (word F v Ω)⟫_ℂ = 0 := by
            rw [← inner_conj_symm, hadj, hΩ, inner_zero_right, map_zero]
          simp [word, wick, hz, gramConstant]
  | cons i u ih =>
      have hu' : u.length ≤ L := by simp only [List.length_cons] at hu; omega
      have step := annihilator_word_error_le F A Ω hΩ i v ε hε (herr i v hv)
      let S : H := ((removeOne i v).map (fun t => word F t Ω)).sum
      have hfirst :
          ‖⟪word F u Ω, A i (word F v Ω)⟫_ℂ - ⟪word F u Ω, S⟫_ℂ‖ ≤
            B * ((v.length : ℝ) * ε) := by
        rw [← inner_sub_right]
        exact (norm_inner_le_norm _ _).trans (mul_le_mul
          (hword u hu') step (norm_nonneg _) hB)
      have hsum :
          ‖⟪word F u Ω, S⟫_ℂ - (wick (i :: u) v : ℂ)‖ ≤
            (v.length : ℝ) * ((gramConstant L u.length : ℝ) * B * ε) := by
        have hi : ∀ t ∈ removeOne i v,
            ‖⟪word F u Ω, word F t Ω⟫_ℂ - (wick u t : ℂ)‖ ≤
              (gramConstant L u.length : ℝ) * B * ε := by
          intro t ht
          exact ih t hu' (by have := length_of_mem_removeOne i v t ht; omega)
        have hc : 0 ≤ (gramConstant L u.length : ℝ) * B * ε := by positivity
        have hh := complex_list_sum_bound (removeOne i v)
          (fun t => ⟪word F u Ω, word F t Ω⟫_ℂ)
          (fun t => (wick u t : ℂ)) _ hc hi
        have castSum : (wick (i :: u) v : ℂ) =
            ((removeOne i v).map (fun t => (wick u t : ℂ))).sum := by
          simp [wick, Function.comp_def]
        rw [castSum]
        dsimp [S]
        rw [inner_list_sum, List.map_map]
        exact hh.trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast removeOne_length_le i v) hc)
      calc
        _ = ‖⟪word F u Ω, A i (word F v Ω)⟫_ℂ - (wick (i :: u) v : ℂ)‖ := by
          rw [word_cons, hadj]
        _ ≤ ‖⟪word F u Ω, A i (word F v Ω)⟫_ℂ - ⟪word F u Ω, S⟫_ℂ‖ +
              ‖⟪word F u Ω, S⟫_ℂ - (wick (i :: u) v : ℂ)‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            ⟪word F u Ω, A i (word F v Ω)⟫_ℂ ⟪word F u Ω, S⟫_ℂ (wick (i :: u) v : ℂ)
        _ ≤ B * ((v.length : ℝ) * ε) +
              (v.length : ℝ) * ((gramConstant L u.length : ℝ) * B * ε) :=
          add_le_add hfirst hsum
        _ = (v.length : ℝ) * ((gramConstant L u.length : ℝ) + 1) * B * ε := by ring
        _ ≤ (L : ℝ) * ((gramConstant L u.length : ℝ) + 1) * B * ε := by
          gcongr
        _ = _ := by simp [gramConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- The number of one-letter deletions is precisely the letter multiplicity. -/
theorem removeOne_length (i : ι) (w : List ι) :
    (removeOne i w).length = w.count i := by
  induction w with
  | nil => simp [removeOne]
  | cons j w ih =>
      simp only [removeOne, List.length_append, List.length_map, ih]
      by_cases hij : i = j
      · subst j; simp [Nat.add_comm]
      · simp [hij, Ne.symm hij]

/-- Every deleted word restores the original multiset when `i` is reinserted. -/
theorem perm_cons_of_mem_removeOne (i : ι) (w t : List ι)
    (ht : t ∈ removeOne i w) : (i :: t).Perm w := by
  induction w generalizing t with
  | nil => simp at ht
  | cons j w ih =>
      simp only [removeOne, List.mem_append, List.mem_map] at ht
      rcases ht with ht | ⟨s, hs, rfl⟩
      · split_ifs at ht with hij
        · have htw : t = w := by simpa using ht
          subst t; subst j; exact List.Perm.refl _
        · simp at ht
      · exact (List.Perm.swap _ _ _).trans ((ih s hs).cons j)

/-- Product of root-occupation factorials, given without a finiteness assumption
on the root-label type. -/
def occupationFactorial : List ι → ℕ
  | [] => 1
  | i :: u => (u.count i + 1) * occupationFactorial u

private theorem sum_map_constant {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x = c) : (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.sum_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
      simp [Nat.add_mul, Nat.add_comm]

/-- Wick contractions vanish unless occupations agree, and otherwise equal the
product of the occupation factorials. This proves the bosonic leading term
rather than assuming it as part of the normal-ordering estimate. -/
theorem wick_eq_occupationFactorial (u v : List ι) :
    wick u v = if u.Perm v then occupationFactorial u else 0 := by
  induction u generalizing v with
  | nil => cases v <;> simp [wick, occupationFactorial]
  | cons i u ih =>
      have hterm : ∀ t ∈ removeOne i v,
          wick u t = if (i :: u).Perm v then occupationFactorial u else 0 := by
        intro t ht
        rw [ih]
        have hp := perm_cons_of_mem_removeOne i v t ht
        have heq : u.Perm t ↔ (i :: u).Perm v := by
          constructor
          · intro h; exact (h.cons i).trans hp
          · intro h; exact (List.perm_cons i).mp (h.trans hp.symm)
        simp only [heq]
      rw [wick, sum_map_constant _ _ _ hterm, removeOne_length]
      by_cases hp : (i :: u).Perm v
      · rw [if_pos hp, if_pos hp, occupationFactorial]
        have hc := hp.count_eq i
        simpa using congrArg (fun n => n * occupationFactorial u) hc.symm
      · simp [hp]

/-- For a finite root set this is the usual explicit factorial product. -/
theorem occupationFactorial_eq_prod [Fintype ι] (u : List ι) :
    occupationFactorial u = ∏ i, (u.count i).factorial := by
  induction u with
  | nil => simp [occupationFactorial]
  | cons j u ih =>
      rw [occupationFactorial, ih]
      have hcount : ∀ i, ((j :: u).count i).factorial =
          (if i = j then u.count j + 1 else 1) * (u.count i).factorial := by
        intro i
        by_cases hij : i = j
        · subst i; simp [Nat.factorial_succ]
        · simp [hij, Ne.symm hij]
      simp_rw [hcount]
      rw [Finset.prod_mul_distrib]
      simp

/-- Explicit leading Gram matrix for any finite collection of roots. -/
theorem wick_eq_factorial_product [Fintype ι] (u v : List ι) :
    wick u v = if u.Perm v then ∏ i, (u.count i).factorial else 0 := by
  rw [wick_eq_occupationFactorial, occupationFactorial_eq_prod]

end Cloning.PBW
