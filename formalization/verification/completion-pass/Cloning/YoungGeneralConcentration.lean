import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite-alphabet concentration, with an explicit finite sum

The probability space consists of actual words over a finite alphabet.  The
proof calculates their exponential moment and applies a pointwise exponential
bound; no concentration estimate is supplied as an assumption.  This is the
analytic input for the tableau formula for the general Young law.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungGeneral

def wordWeight {d N : ℕ} (p : Fin d → ℝ) (w : Fin N → Fin d) : ℝ :=
  ∏ k, p (w k)

def rowCount {d N : ℕ} (w : Fin N → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun k ↦ w k = i)).card

theorem wordWeight_nonneg {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (w : Fin N → Fin d) : 0 ≤ wordWeight p w :=
  Finset.prod_nonneg (fun k _ ↦ hp (w k))

theorem wordWeight_sum {d N : ℕ} (p : Fin d → ℝ) (hp : ∑ i, p i = 1) :
    (∑ w : Fin N → Fin d, wordWeight p w) = 1 := by
  simp only [wordWeight]
  rw [← Fintype.sum_pow, hp, one_pow]

theorem wordWeight_eq_row_product {d N : ℕ} (p : Fin d → ℝ)
    (w : Fin N → Fin d) : wordWeight p w = ∏ i, p i ^ rowCount w i := by
  classical
  simpa [wordWeight, rowCount, Fintype.card_subtype] using (Fintype.prod_fiberwise' w p).symm

theorem sum_rowCount {d N : ℕ} (w : Fin N → Fin d) : ∑ i, rowCount w i = N := by
  classical
  simpa [rowCount, Fintype.card_subtype] using (Fintype.sum_fiberwise w (fun _ ↦ (1 : ℕ)))

private theorem exp_le_quadratic {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (show ‖x‖ ≤ 1 by simpa using hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h
  have := (abs_le.mp h).2
  linarith

/-- A finite centered variable in `[-1,1]` has this elementary MGF bound
for parameters of absolute value at most one. -/
theorem finite_mgf_le {d : ℕ} (p x : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hx : ∀ i, |x i| ≤ 1) (hm : ∑ i, p i * x i = 0)
    (t : ℝ) (ht : |t| ≤ 1) :
    (∑ i, p i * Real.exp (t * x i)) ≤ Real.exp (t ^ 2) := by
  have hb i : Real.exp (t * x i) ≤ 1 + t * x i + t ^ 2 := by
    have htx : |t * x i| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul ht (hx i) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hsqi : (x i) ^ 2 ≤ 1 := by nlinarith [(abs_le.mp (hx i)).1, (abs_le.mp (hx i)).2]
    have := mul_le_mul_of_nonneg_left hsqi (sq_nonneg t)
    nlinarith [exp_le_quadratic htx]
  calc
    _ ≤ ∑ i, p i * (1 + t * x i + t ^ 2) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hb i) (hp i))
    _ = 1 + t ^ 2 := by
      simp_rw [mul_add, mul_one, show ∀ i, p i * (t * x i) = t * (p i * x i) by intro i; ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hs, hm]
      ring
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (t ^ 2)

/-- Exact independent-product generating function. -/
theorem word_mgf_eq {d N : ℕ} (p x : Fin d → ℝ) (t : ℝ) :
    (∑ w : Fin N → Fin d, wordWeight p w * Real.exp (t * ∑ k, x (w k))) =
      (∑ i, p i * Real.exp (t * x i)) ^ N := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro w _
  rw [wordWeight, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum]

theorem word_mgf_le {d N : ℕ} (p x : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hx : ∀ i, |x i| ≤ 1) (hm : ∑ i, p i * x i = 0)
    (t : ℝ) (ht : |t| ≤ 1) :
    (∑ w : Fin N → Fin d, wordWeight p w * Real.exp (t * ∑ k, x (w k))) ≤
      Real.exp ((N : ℝ) * t ^ 2) := by
  rw [word_mgf_eq]
  calc
    _ ≤ Real.exp (t ^ 2) ^ N := pow_le_pow_left₀
      (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hp i) (Real.exp_pos _).le))
      (finite_mgf_le p x hp hs hx hm t ht) N
    _ = _ := by rw [← Real.exp_nat_mul]

/-- A one-sided bound valid uniformly in the alphabet probabilities. -/
theorem word_tail_le {d N : ℕ} (p x : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hx : ∀ i, |x i| ≤ 1) (hm : ∑ i, p i * x i = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    (∑ w : Fin N → Fin d,
      if (N : ℝ) * ε ≤ ∑ k, x (w k) then wordWeight p w else 0) ≤
      Real.exp (-(N : ℝ) * ε ^ 2 / 4) := by
  classical
  let t := ε / 2
  have ht : |t| ≤ 1 := by dsimp [t]; rw [abs_of_nonneg (by positivity)]; linarith
  have hpoint (w : Fin N → Fin d) :
      (if (N : ℝ) * ε ≤ ∑ k, x (w k) then wordWeight p w else 0) ≤
        Real.exp (-t * (N : ℝ) * ε) *
          (wordWeight p w * Real.exp (t * ∑ k, x (w k))) := by
    split_ifs with h
    · have hexp : (1 : ℝ) ≤ Real.exp (-t * (N : ℝ) * ε + t * ∑ k, x (w k)) := by
        apply Real.one_le_exp_iff.mpr
        have := mul_le_mul_of_nonneg_left h (show 0 ≤ t by dsimp [t]; positivity)
        linarith
      have hb := mul_le_mul_of_nonneg_left hexp (wordWeight_nonneg p hp w)
      rw [Real.exp_add] at hb
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (wordWeight_nonneg p hp w) (Real.exp_pos _).le)
  calc
    _ ≤ ∑ w : Fin N → Fin d, Real.exp (-t * (N : ℝ) * ε) *
        (wordWeight p w * Real.exp (t * ∑ k, x (w k))) :=
      Finset.sum_le_sum (fun w _ ↦ hpoint w)
    _ = Real.exp (-t * (N : ℝ) * ε) *
        (∑ w : Fin N → Fin d, wordWeight p w * Real.exp (t * ∑ k, x (w k))) :=
      (Finset.mul_sum ..).symm
    _ ≤ Real.exp (-t * (N : ℝ) * ε) * Real.exp ((N : ℝ) * t ^ 2) :=
      mul_le_mul_of_nonneg_left (word_mgf_le p x hp hs hx hm t ht) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring

/-- Centered occupation indicator for one letter. -/
def centeredIndicator {d : ℕ} (p : Fin d → ℝ) (i j : Fin d) : ℝ :=
  (if j = i then 1 else 0) - p i

theorem probability_le_one {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (i : Fin d) : p i ≤ 1 := by
  rw [← hs]
  exact Finset.single_le_sum (fun j _ ↦ hp j) (Finset.mem_univ i)

theorem centeredIndicator_abs_le {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (i j : Fin d) :
    |centeredIndicator p i j| ≤ 1 := by
  have h := probability_le_one p hp hs i
  have h0 := hp i
  unfold centeredIndicator
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem centeredIndicator_mean {d : ℕ} (p : Fin d → ℝ)
    (hs : ∑ i, p i = 1) (i : Fin d) :
    ∑ j, p j * centeredIndicator p i j = 0 := by
  classical
  simp only [centeredIndicator, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hs]
  simp

theorem centeredIndicator_sum {d N : ℕ} (p : Fin d → ℝ)
    (i : Fin d) (w : Fin N → Fin d) :
    (∑ k, centeredIndicator p i (w k)) = (rowCount w i : ℝ) - N * p i := by
  classical
  simp [centeredIndicator, rowCount, Finset.sum_sub_distrib, Finset.sum_boole]

/-- Two-sided deviation of one empirical frequency. -/
theorem rowCount_tail_le {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) (i : Fin d) :
    (∑ w : Fin N → Fin d,
      if (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0) ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 4) := by
  classical
  let x := centeredIndicator p i
  have hp1 := word_tail_le (N := N) p x hp hs
    (centeredIndicator_abs_le p hp hs i) (centeredIndicator_mean p hs i) ε hε hε2
  have hn1 := word_tail_le (N := N) p (fun j ↦ -x j) hp hs
    (fun j ↦ by simpa using centeredIndicator_abs_le p hp hs i j)
    (by simp only [mul_neg, Finset.sum_neg_distrib, centeredIndicator_mean p hs i, neg_zero, x])
    ε hε hε2
  have hpoint (w : Fin N → Fin d) :
      (if (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0) ≤
      (if (N : ℝ) * ε ≤ ∑ k, x (w k) then wordWeight p w else 0) +
      (if (N : ℝ) * ε ≤ ∑ k, -x (w k) then wordWeight p w else 0) := by
    simp only [x, centeredIndicator_sum, Finset.sum_neg_distrib]
    have hw := wordWeight_nonneg p hp w
    split_ifs <;> simp_all only [not_le, le_abs, neg_sub, false_or] <;> first | contradiction | linarith
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin N → Fin d))) ↦ hpoint w)
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- The sup-coordinate tail for the genuine IID word law, uniformly in `p`. -/
theorem max_rowCount_tail_le {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    (∑ w : Fin N → Fin d,
      if ∃ i, (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0) ≤
      2 * d * Real.exp (-(N : ℝ) * ε ^ 2 / 4) := by
  classical
  have hpoint (w : Fin N → Fin d) :
      (if ∃ i, (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0) ≤
      ∑ i, if (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0 := by
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun j ↦ if (N : ℝ) * ε ≤ |(rowCount w j : ℝ) - N * p j| then wordWeight p w else 0)
        (fun j _ ↦ by have := wordWeight_nonneg p hp w; positivity)
        (Finset.mem_univ i)
      simpa only [if_pos hi] using hh
    · exact Finset.sum_nonneg (fun i _ ↦ by have := wordWeight_nonneg p hp w; positivity)
  calc
    _ ≤ ∑ w : Fin N → Fin d, ∑ i,
        if (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0 :=
      Finset.sum_le_sum (fun w _ ↦ hpoint w)
    _ = ∑ i, ∑ w : Fin N → Fin d,
        if (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _i : Fin d, 2 * Real.exp (-(N : ℝ) * ε ^ 2 / 4) :=
      Finset.sum_le_sum (fun i _ ↦ rowCount_tail_le p hp hs ε hε hε2 i)
    _ = _ := by simp; ring

end Cloning.YoungGeneral
