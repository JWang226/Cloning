import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite dominance and strict squared-norm separation.  These elementary
lemmas distinguish the highest shifted weight in the Casimir character
equation; they assume no representation or character formula. -/
noncomputable section
open scoped BigOperators Classical

namespace Cloning.WeylCharacter

def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

@[simp] theorem partialSum_zero (a : ℕ → ℝ) : partialSum a 0 = 0 := by
  simp [partialSum]

theorem partialSum_succ (a : ℕ → ℝ) (n : ℕ) :
    partialSum a (n+1) = partialSum a n + a n := Finset.sum_range_succ _ _

theorem finite_summation_by_parts (a w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i * w i) = partialSum a n * w n +
      ∑ k ∈ Finset.range n, partialSum a (k+1) * (w k - w (k+1)) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, partialSum_succ]
    ring

/-- A strictly decreasing test weight detects every nonzero sequence whose
proper partial sums are nonnegative and whose total is zero. -/
theorem weighted_sum_eq_zero_forces_zero (a w : ℕ → ℝ) (n : ℕ)
    (hpartial : ∀ k ≤ n, 0 ≤ partialSum a k) (htotal : partialSum a n = 0)
    (hw : ∀ k, k+1 < n → w (k+1) < w k)
    (hweighted : ∑ i ∈ Finset.range n, a i * w i = 0) :
    ∀ i < n, a i = 0 := by
  have hnonneg (k : ℕ) (hk : k ∈ Finset.range n) :
      0 ≤ partialSum a (k+1) * (w k - w (k+1)) := by
    have hkn : k < n := Finset.mem_range.mp hk
    by_cases hlast : k+1 = n
    · rw [hlast, htotal, zero_mul]
    · exact mul_nonneg (hpartial (k+1) (by omega)) (sub_nonneg.mpr (hw k (by omega)).le)
  have hsum : (∑ k ∈ Finset.range n, partialSum a (k+1) * (w k - w (k+1))) = 0 := by
    rw [finite_summation_by_parts a w n, htotal, zero_mul, zero_add] at hweighted
    exact hweighted
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  have hpzero (k : ℕ) (hk : k ≤ n) : partialSum a k = 0 := by
    by_cases hk0 : k = 0
    · subst k; exact partialSum_zero a
    by_cases hkn : k = n
    · rw [hkn, htotal]
    have hkpos : 0 < k := by omega
    have h := hterm (k-1) (Finset.mem_range.mpr (by omega))
    rw [show k-1+1=k by omega] at h
    have hw' := hw (k-1) (by omega)
    rw [show k-1+1=k by omega] at hw'
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (ne_of_gt hw'))
  intro i hi
  have h := partialSum_succ a i
  rw [hpzero (i+1) (by omega), hpzero i (by omega), zero_add] at h
  exact h.symm

/-- Dominance and the squared-norm eigenvalue determine a strictly dominant
weight uniquely among dominant weights. -/
theorem dominant_eq_of_sum_squares (a b : ℕ → ℝ) (n : ℕ)
    (ha : ∀ k, k+1 < n → a (k+1) < a k)
    (hb : ∀ k, k+1 < n → b (k+1) ≤ b k)
    (hprefix : ∀ k ≤ n, partialSum b k ≤ partialSum a k)
    (htotal : partialSum a n = partialSum b n)
    (hsq : ∑ i ∈ Finset.range n, a i ^ 2 = ∑ i ∈ Finset.range n, b i ^ 2) :
    ∀ i < n, a i = b i := by
  have hp k : partialSum (fun i ↦ a i - b i) k = partialSum a k - partialSum b k := by
    simp [partialSum, Finset.sum_sub_distrib]
  have hc := weighted_sum_eq_zero_forces_zero (fun i ↦ a i - b i)
    (fun i ↦ a i + b i) n
    (fun k hk ↦ by rw [hp]; exact sub_nonneg.mpr (hprefix k hk))
    (by rw [hp, htotal, sub_self])
    (fun k hk ↦ by have := ha k hk; have := hb k hk; linarith)
    (by
      simp_rw [show ∀ i, (a i - b i) * (a i + b i) = a i ^ 2 - b i ^ 2 by intro i; ring]
      rw [Finset.sum_sub_distrib, hsq, sub_self])
  intro i hi
  exact sub_eq_zero.mp (hc i hi)

def zeroExtend {d : ℕ} (a : Fin d → ℝ) (k : ℕ) : ℝ :=
  if hk : k < d then a ⟨k, hk⟩ else 0

@[simp] theorem zeroExtend_apply {d : ℕ} (a : Fin d → ℝ) (i : Fin d) :
    zeroExtend a i.val = a i := by simp [zeroExtend, i.isLt]

theorem sum_zeroExtend {d : ℕ} (a : Fin d → ℝ) :
    partialSum (zeroExtend a) d = ∑ i, a i := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  simp only [zeroExtend_apply]

def DominatedBy {d : ℕ} (b a : Fin d → ℝ) : Prop :=
  (∀ k ≤ d, partialSum (zeroExtend b) k ≤ partialSum (zeroExtend a) k) ∧
    (∑ i, b i) = ∑ i, a i

theorem fin_dominant_eq_of_sum_squares {d : ℕ} (a b : Fin d → ℝ)
    (ha : StrictAnti a) (hb : Antitone b) (hdom : DominatedBy b a)
    (hsq : ∑ i, a i ^ 2 = ∑ i, b i ^ 2) : a = b := by
  have h := dominant_eq_of_sum_squares (zeroExtend a) (zeroExtend b) d
    (fun k hk ↦ by
      simpa only [zeroExtend, dif_pos hk, dif_pos (show k < d by omega)] using
        ha (show (⟨k, by omega⟩ : Fin d) < ⟨k+1, hk⟩ from by simp))
    (fun k hk ↦ by
      simpa only [zeroExtend, dif_pos hk, dif_pos (show k < d by omega)] using
        hb (show (⟨k, by omega⟩ : Fin d) ≤ ⟨k+1, hk⟩ from by simp))
    hdom.1 (by simpa only [sum_zeroExtend] using hdom.2.symm)
    (by simpa only [← Fin.sum_univ_eq_sum_range, zeroExtend_apply] using hsq)
  funext i
  simpa only [zeroExtend_apply] using h i.val i.isLt

end Cloning.WeylCharacter
