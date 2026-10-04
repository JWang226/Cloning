import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The bounded squaring recurrence

A bounded real function whose square is controlled by its value at a successor
cannot have absolute value larger than one.  The anisotropic Gaussian update
below supplies the exact normalization identity used with that recurrence.
-/

noncomputable section
open scoped BigOperators

namespace Cloning.UniversalLeastNoise

/-- A uniformly upper-bounded squaring recurrence forces a universal bound of
one. No convergence of the successor iterates and no positivity of `J` is
required. -/
theorem abs_le_one_of_sq_le_next {α : Type*} (T : α → α) (J : α → ℝ)
    (hbounded : BddAbove (Set.range J)) (hsq : ∀ a, J a ^ 2 ≤ J (T a))
    (a : α) : |J a| ≤ 1 := by
  let S := sSup (Set.range J)
  have hle (b : α) : J b ≤ S := le_csSup hbounded (Set.mem_range_self b)
  have hS : S ≤ 1 := by
    by_contra h
    have hS1 : 1 < S := lt_of_not_ge h
    obtain ⟨j, ⟨b, rfl⟩, hj⟩ :=
      exists_lt_of_lt_csSup (show (Set.range J).Nonempty from ⟨J a, ⟨a, rfl⟩⟩) (show (S + 1) / 2 < S by linarith)
    have hbj : 0 < J b := by linarith
    have hrec := (hsq b).trans (hle (T b))
    nlinarith [sq_nonneg (S - 1)]
  have hrec := (hsq a).trans ((hle (T a)).trans hS)
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (J a + 1)],
    by nlinarith [sq_nonneg (J a - 1)]⟩

/-- A supplied finite scalar bound is sufficient for the recurrence theorem. -/
theorem abs_le_one_of_sq_le_next_of_bound {α : Type*} (T : α → α) (J : α → ℝ)
    (C : ℝ) (hbound : ∀ a, J a ≤ C) (hsq : ∀ a, J a ^ 2 ≤ J (T a))
    (a : α) : |J a| ≤ 1 :=
  abs_le_one_of_sq_le_next T J ⟨C, by rintro _ ⟨a, rfl⟩; exact hbound a⟩ hsq a

/-- The one-coordinate Gaussian update. -/
def gaussianUpdate (h t : ℝ) : ℝ := (t ^ 2 + h ^ 2) / (2 * t)

/-- The update preserves the closed physical domain `t ≥ h > 0`. -/
theorem le_gaussianUpdate {h t : ℝ} (hh : 0 < h) (ht : h ≤ t) :
    h ≤ gaussianUpdate h t := by
  have ht0 : 0 < t := lt_of_lt_of_le hh ht
  unfold gaussianUpdate
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  nlinarith [sq_nonneg (t - h)]

/-- The update decreases the Gaussian width. -/
theorem gaussianUpdate_le {h t : ℝ} (hh : 0 < h) (ht : h ≤ t) :
    gaussianUpdate h t ≤ t := by
  have ht0 : 0 < t := lt_of_lt_of_le hh ht
  unfold gaussianUpdate
  apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
  nlinarith

/-- Exact normalization identity for a single Gaussian factor. -/
theorem gaussianUpdate_normalization {h t : ℝ} (ht : t ≠ 0) :
    (t + h) ^ 2 = 2 * t * (gaussianUpdate h t + h) := by
  unfold gaussianUpdate
  field_simp
  ring

/-- The distance to the fixed point contracts by at least one half. -/
theorem gaussianUpdate_sub_le_half {h t : ℝ} (hh : 0 < h) (ht : h ≤ t) :
    gaussianUpdate h t - h ≤ (t - h) / 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le hh ht
  have hnorm := gaussianUpdate_normalization (h := h) ht0.ne'
  nlinarith [mul_nonneg hh.le (sub_nonneg.mpr ht)]

/-- Coordinatewise Gaussian widths above their positive physical thresholds. -/
def GaussianWidths {ι : Type*} (h : ι → ℝ) := {t : ι → ℝ // ∀ i, h i ≤ t i}

/-- The update is a genuine self-map of the anisotropic physical domain. -/
def updateWidths {ι : Type*} {h : ι → ℝ} (hh : ∀ i, 0 < h i)
    (t : GaussianWidths h) : GaussianWidths h :=
  ⟨fun i => gaussianUpdate (h i) (t.1 i),
    fun i => le_gaussianUpdate (hh i) (t.2 i)⟩

/-- Normalization identity for every finite collection of Gaussian modes. -/
theorem gaussianUpdate_prod_normalization {ι : Type*} [Fintype ι]
    (h t : ι → ℝ) (ht : ∀ i, t i ≠ 0) :
    (∏ i, (t i + h i)) ^ 2 =
      (∏ i, (2 * t i)) * (∏ i, (gaussianUpdate (h i) (t i) + h i)) := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => gaussianUpdate_normalization (ht i))

/-- Inverse of the sharp anisotropic Gaussian integral bound. -/
def gaussianNormalization {ι : Type*} [Fintype ι] (P : ℝ) (h t : ι → ℝ) : ℝ :=
  ∏ i, (t i + h i) / P

/-- Elementary absolute-integral bound before using positivity. -/
def gaussianL1Bound {ι : Type*} [Fintype ι] (P : ℝ) (t : ι → ℝ) : ℝ :=
  ∏ i, P / t i

/-- Scalar factor in the Gaussian convolution recurrence. -/
def gaussianConvolutionFactor {ι : Type*} [Fintype ι] (P : ℝ) (t : ι → ℝ) : ℝ :=
  ∏ i, P / (2 * t i)

/-- Sharp bound for the anisotropic Gaussian integral. -/
def gaussianSharpBound {ι : Type*} [Fintype ι] (P : ℝ) (h t : ι → ℝ) : ℝ :=
  ∏ i, P / (t i + h i)

/-- The normalizing factor is strictly positive throughout the physical domain. -/
theorem gaussianNormalization_pos {ι : Type*} [Fintype ι] {P : ℝ}
    (hP : 0 < P) {h t : ι → ℝ} (hh : ∀ i, 0 < h i) (ht : ∀ i, h i ≤ t i) :
    0 < gaussianNormalization P h t := by
  apply Finset.prod_pos
  intro i _
  exact div_pos (add_pos (lt_of_lt_of_le (hh i) (ht i)) (hh i)) hP

/-- The normalized elementary bound is uniformly bounded by two per mode. -/
theorem gaussianNormalization_mul_L1Bound_le {ι : Type*} [Fintype ι] {P : ℝ}
    (hP : 0 < P) {h t : ι → ℝ} (hh : ∀ i, 0 < h i) (ht : ∀ i, h i ≤ t i) :
    gaussianNormalization P h t * gaussianL1Bound P t ≤ (2 : ℝ) ^ Fintype.card ι := by
  unfold gaussianNormalization gaussianL1Bound
  rw [← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _i : ι, (2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (div_nonneg (add_nonneg (le_of_lt (lt_of_lt_of_le (hh i) (ht i)))
          (hh i).le) hP.le) (div_nonneg hP.le (le_of_lt (lt_of_lt_of_le (hh i) (ht i))))
      · intro i _
        have ht0 := lt_of_lt_of_le (hh i) (ht i)
        have heq : ((t i + h i) / P) * (P / t i) = (t i + h i) / t i := by
          field_simp
        rw [heq]
        apply (div_le_iff₀ ht0).mpr
        linarith [ht i]
    _ = _ := by simp

/-- The normalizing factor cancels the convolution constant exactly. -/
theorem gaussianNormalization_sq_mul_convolution {ι : Type*} [Fintype ι] {P : ℝ}
    (hP : P ≠ 0) (h t : ι → ℝ) (ht : ∀ i, t i ≠ 0) :
    gaussianNormalization P h t ^ 2 * gaussianConvolutionFactor P t =
      gaussianNormalization P h (fun i => gaussianUpdate (h i) (t i)) := by
  unfold gaussianNormalization gaussianConvolutionFactor
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold gaussianUpdate
  field_simp [ht i]
  ring

/-- The sharp bound is the exact reciprocal of the normalizing factor. -/
theorem gaussianNormalization_mul_sharpBound {ι : Type*} [Fintype ι] {P : ℝ}
    (hP : P ≠ 0) (h t : ι → ℝ) (ht : ∀ i, t i + h i ≠ 0) :
    gaussianNormalization P h t * gaussianSharpBound P h t = 1 := by
  unfold gaussianNormalization gaussianSharpBound
  rw [← Finset.prod_mul_distrib]
  convert Finset.prod_const_one (s := Finset.univ) using 1
  apply Finset.prod_congr rfl
  intro i _
  field_simp [ht i]

/-- Convert a unit bound after normalization into the sharp product bound. -/
theorem abs_le_gaussianSharpBound_of_normalized {ι : Type*} [Fintype ι] {P : ℝ}
    (hP : 0 < P) {h t : ι → ℝ} (hh : ∀ i, 0 < h i) (ht : ∀ i, h i ≤ t i)
    {x : ℝ} (hx : |gaussianNormalization P h t * x| ≤ 1) :
    |x| ≤ gaussianSharpBound P h t := by
  have hc := gaussianNormalization_pos hP hh ht
  have hnorm := gaussianNormalization_mul_sharpBound hP.ne' h t
    (fun i => (add_pos (lt_of_lt_of_le (hh i) (ht i)) (hh i)).ne')
  rw [abs_mul, abs_of_pos hc] at hx
  exact (mul_le_mul_iff_right₀ hc).mp (hx.trans_eq hnorm.symm)

/-- Gaussian convolution and the elementary absolute-integral bound imply the
sharp product estimate. This result uses no limit or compactness argument. -/
theorem gaussianSharpBound_of_convolution {ι : Type*} [Fintype ι] {P : ℝ}
    (hP : 0 < P) {h : ι → ℝ} (hh : ∀ i, 0 < h i)
    (J : GaussianWidths h → ℝ)
    (hL1 : ∀ t, J t ≤ gaussianL1Bound P t.1)
    (hconv : ∀ t, J t ^ 2 ≤ gaussianConvolutionFactor P t.1 * J (updateWidths hh t))
    (t : GaussianWidths h) :
    |J t| ≤ gaussianSharpBound P h t.1 := by
  apply abs_le_gaussianSharpBound_of_normalized hP hh t.2
  apply abs_le_one_of_sq_le_next_of_bound (updateWidths hh)
    (fun t => gaussianNormalization P h t.1 * J t) ((2 : ℝ) ^ Fintype.card ι)
  · intro u
    exact (mul_le_mul_of_nonneg_left (hL1 u)
      (gaussianNormalization_pos hP hh u.2).le).trans
      (gaussianNormalization_mul_L1Bound_le hP hh u.2)
  · intro u
    have hstep := mul_le_mul_of_nonneg_left (hconv u)
      (sq_nonneg (gaussianNormalization P h u.1))
    rw [mul_pow]
    convert hstep using 1
    rw [← mul_assoc, gaussianNormalization_sq_mul_convolution hP.ne' h u.1
      (fun i => (lt_of_lt_of_le (hh i) (u.2 i)).ne')]
    rfl

end Cloning.UniversalLeastNoise
