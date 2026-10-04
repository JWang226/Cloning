import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Exact Cartan occupation coefficient calculations

The scalar coefficients in `eq:cartan-coefficients` of `cloning.tex` have
binomial squares. We prove their normalization, their thermal moments, and
the corresponding identities for any finite collection of roots. These
are exact finite identities, with no assumptions about limiting quantum
channels. The identification of the representation-theoretic coefficients
with this formula remains a separate obligation.
-/

namespace Cloning.Occupation

noncomputable section

open scoped BigOperators
open Finset

/-- Square of the one-root Cartan splitting coefficient. -/
def splitWeight (r a : ℕ) (s : ℝ) : ℝ :=
  (r.choose a : ℝ) * s ^ a * (1 - s) ^ (r - a)

theorem splitWeight_nonneg (r a : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ splitWeight r a s := by
  unfold splitWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))
    (pow_nonneg (sub_nonneg.mpr hs1) _)

/-- Exact finite thermal moment used in `eq:sector-output-fixed-matrix`. -/
theorem splitWeight_moment (r : ℕ) (s q : ℝ) :
    (∑ a ∈ range (r + 1), splitWeight r a s * q ^ a) =
      (1 - s + s * q) ^ r := by
  rw [show 1 - s + s * q = s * q + (1 - s) by ring, add_pow]
  apply sum_congr rfl
  intro a ha
  simp only [splitWeight, mul_pow]
  ring

/-- The one-root squared splitting coefficients sum to one. -/
theorem splitWeight_sum (r : ℕ) (s : ℝ) :
    (∑ a ∈ range (r + 1), splitWeight r a s) = 1 := by
  simpa using splitWeight_moment r s 1

theorem splitWeight_moment_fin (r : ℕ) (s q : ℝ) :
    (∑ a : Fin (r + 1), splitWeight r a s * q ^ (a : ℕ)) =
      (1 - s + s * q) ^ r := by
  rw [Fin.sum_univ_eq_sum_range (fun a => splitWeight r a s * q ^ a)]
  exact splitWeight_moment r s q

theorem splitWeight_sum_fin (r : ℕ) (s : ℝ) :
    (∑ a : Fin (r + 1), splitWeight r a s) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun a => splitWeight r a s)]
  exact splitWeight_sum r s

/-- The nonnegative Cartan coefficient for one root. -/
def splitAmplitude (r a : ℕ) (s : ℝ) : ℝ := Real.sqrt (splitWeight r a s)

theorem splitAmplitude_sq (r a : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    splitAmplitude r a s ^ 2 = splitWeight r a s :=
  Real.sq_sqrt (splitWeight_nonneg r a hs0 hs1)

theorem splitAmplitude_sq_sum (r : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑ a : Fin (r + 1), splitAmplitude r a s ^ 2) = 1 := by
  simp_rw [splitAmplitude_sq _ _ hs0 hs1]
  exact splitWeight_sum_fin r s

section Multimode

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multi-root splitting coefficient, with `a i ≤ r i` encoded in its type. -/
def cartanAmplitude (r : ι → ℕ) (s : ι → ℝ) (a : ∀ i, Fin (r i + 1)) : ℝ :=
  ∏ i, splitAmplitude (r i) (a i) (s i)

omit [DecidableEq ι] in
theorem cartanAmplitude_sq (r : ι → ℕ) (s : ι → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1)
    (a : ∀ i, Fin (r i + 1)) :
    cartanAmplitude r s a ^ 2 = ∏ i, splitWeight (r i) (a i) (s i) := by
  unfold cartanAmplitude
  rw [← Finset.prod_pow]
  apply prod_congr rfl
  intro i hi
  exact splitAmplitude_sq _ _ (hs0 i) (hs1 i)

/-- Exact normalization of the multi-root Cartan coefficient vector. -/
theorem cartanAmplitude_sq_sum (r : ι → ℕ) (s : ι → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    (∑ a : ∀ i, Fin (r i + 1), cartanAmplitude r s a ^ 2) = 1 := by
  simp_rw [cartanAmplitude_sq r s hs0 hs1]
  rw [← Fintype.prod_sum (fun i (a : Fin (r i + 1)) => splitWeight (r i) a (s i))]
  simp_rw [splitWeight_sum_fin]
  simp

/-- The multi-root finite thermal moment appearing in the sector-output calculation. -/
theorem cartanAmplitude_thermal_moment (r : ι → ℕ) (s q : ι → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    (∑ a : ∀ i, Fin (r i + 1),
      cartanAmplitude r s a ^ 2 * ∏ i, q i ^ (a i : ℕ)) =
      ∏ i, (1 - s i + s i * q i) ^ r i := by
  simp_rw [cartanAmplitude_sq r s hs0 hs1, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum
    (fun i (a : Fin (r i + 1)) => splitWeight (r i) a (s i) * q i ^ (a : ℕ))]
  apply prod_congr rfl
  intro i hi
  exact splitWeight_moment_fin (r i) (s i) (q i)

end Multimode

/-- Finite negative-binomial convolution. The specialization `a = D - 2`,
`b = n`, `k = m - n` normalizes Werner's occupation law after grouping
occupation vectors by their total excitation number. -/
theorem choose_convolution (a b k : ℕ) :
    (∑ t ∈ range (k + 1), (t + a).choose a * (k - t + b).choose b) =
      (k + a + b + 1).choose (a + b + 1) := by
  induction a generalizing k with
  | zero =>
    simp only [Nat.add_zero, Nat.choose_zero_right, one_mul, Nat.zero_add]
    rw [← Finset.sum_flip]
    calc
      _ = ∑ t ∈ range (k + 1), (t + b).choose b := by
        apply sum_congr rfl
        intro t ht
        rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (mem_range.mp ht))]
      _ = _ := Nat.sum_range_add_choose k b
  | succ a ih =>
    induction k with
    | zero => simp
    | succ k hk =>
      have hsplit :
          (∑ t ∈ range (k + 1 + 1), (t + (a + 1)).choose (a + 1) *
            (k + 1 - t + b).choose b) =
          (∑ t ∈ range (k + 1 + 1), (t + a).choose a *
            (k + 1 - t + b).choose b) +
          (∑ t ∈ range (k + 1 + 1), (t + a).choose (a + 1) *
            (k + 1 - t + b).choose b) := by
        simp_rw [← Nat.add_assoc, Nat.choose_succ_succ, add_mul, sum_add_distrib]
      rw [hsplit, ih]
      have hshift :
          (∑ t ∈ range (k + 1 + 1), (t + a).choose (a + 1) *
            (k + 1 - t + b).choose b) =
          (∑ t ∈ range (k + 1), (t + (a + 1)).choose (a + 1) *
            (k - t + b).choose b) := by
        rw [sum_range_succ']
        simp only [Nat.zero_add, Nat.choose_succ_self, zero_mul, add_zero]
        apply sum_congr rfl
        intro t ht
        simp [Nat.add_comm, Nat.add_left_comm]
      rw [hshift, hk]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ (k + a + b + 2) (a + b + 1)).symm

/-- Exact finite normalization numerator for Werner's occupation law,
including the number of occupation vectors with a given total `t`. -/
theorem werner_occupation_numerator (n m D : ℕ) (hnm : n ≤ m) (hD : 2 ≤ D) :
    (∑ t ∈ range (m - n + 1),
      (t + D - 2).choose (D - 2) * (m - t).choose n) =
      (m + D - 1).choose (n + D - 1) := by
  have htop : m - n + (D - 2) + n + 1 = m + D - 1 := by omega
  have hbottom : D - 2 + n + 1 = n + D - 1 := by omega
  rw [← htop, ← hbottom, ← choose_convolution]
  apply sum_congr rfl
  intro t ht
  have ht' : t ≤ m - n := Nat.lt_succ_iff.mp (mem_range.mp ht)
  congr 2 <;> omega

/-- The eigenvalue attached to any occupation vector of total size `t`
in `eq:occupation-law`. -/
def wernerWeight (n m D t : ℕ) : ℝ :=
  ((m - t).choose n : ℝ) / ((m + D - 1).choose (n + D - 1) : ℝ)

/-- Grouping Werner eigenvalues by total excitation gives total probability
one, for every `m ≥ n` and ambient dimension `D ≥ 2`. -/
theorem werner_occupation_normalization (n m D : ℕ) (hnm : n ≤ m) (hD : 2 ≤ D) :
    (∑ t ∈ range (m - n + 1),
      ((t + D - 2).choose (D - 2) : ℝ) * wernerWeight n m D t) = 1 := by
  have hpos : 0 < (m + D - 1).choose (n + D - 1) :=
    Nat.choose_pos (by omega)
  have hne : ((m + D - 1).choose (n + D - 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hpos)
  simp only [wernerWeight, div_eq_mul_inv, ← mul_assoc, ← sum_mul]
  have hsum :
      (∑ t ∈ range (m - n + 1),
        ((t + D - 2).choose (D - 2) : ℝ) * ((m - t).choose n : ℝ)) =
        ((m + D - 1).choose (n + D - 1) : ℝ) := by
    exact_mod_cast werner_occupation_numerator n m D hnm hD
  rw [hsum, mul_inv_cancel₀ hne]

end

end Cloning.Occupation
