import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform entropy remainder in multinomial central windows

The remainder is bounded explicitly from the power-series remainder for the
logarithm. In particular, no central or local limit theorem is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.YoungMultinomial

/-- The third-order remainder of the elementary entropy function. -/
def entropyRemainder (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2

/-- A numerical third-order bound valid throughout a fixed neighborhood. -/
theorem abs_entropyRemainder_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |entropyRemainder u| ≤ 4 * |u| ^ 3 := by
  have hu1 : |-u| < 1 := by rw [abs_neg]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le hu1 2
  norm_num [Finset.sum_range_succ] at hlog
  have hlog' : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
    have hd : 0 < 1 - |u| := by linarith
    have ht : |u| ^ 3 / (1 - |u|) ≤ 2 * |u| ^ 3 := by
      rw [div_le_iff₀ hd]
      nlinarith [pow_nonneg (abs_nonneg u) 3]
    convert hlog.trans ht using 1 <;> congr 1 <;> ring
  have hab : |1 + u| ≤ 3 / 2 := by
    exact (abs_add_le 1 u).trans (by simpa using (show 1 + |u| ≤ 3 / 2 by linarith))
  have hid : entropyRemainder u =
      (1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2 := by
    unfold entropyRemainder
    ring
  rw [hid]
  calc
    _ ≤ |(1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2)| + |u ^ 3 / 2| :=
      abs_sub _ _
    _ = |1 + u| * |Real.log (1 + u) - u + u ^ 2 / 2| + |u| ^ 3 / 2 := by
      rw [abs_mul, abs_div, abs_pow]
      norm_num
    _ ≤ (3 / 2) * (2 * |u| ^ 3) + |u| ^ 3 / 2 := by gcongr
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

/-- Coordinate entropy after removing its linear and quadratic terms. -/
def coordinateRemainder (p δ : ℝ) : ℝ :=
  (p + δ) * Real.log ((p + δ) / p) - δ - δ ^ 2 / (2 * p)

theorem coordinateRemainder_eq {p : ℝ} (hp : p ≠ 0) (δ : ℝ) :
    coordinateRemainder p δ = p * entropyRemainder (δ / p) := by
  have h : (p + δ) / p = 1 + δ / p := by field_simp
  rw [coordinateRemainder, entropyRemainder, h]
  field_simp

/-- Explicit entropy remainder, uniform as the positive reference coordinate
varies away from zero. -/
theorem abs_coordinateRemainder_le {p δ : ℝ} (hp : 0 < p)
    (hδ : |δ| ≤ p / 2) :
    |coordinateRemainder p δ| ≤ 4 * |δ| ^ 3 / p ^ 2 := by
  have hu : |δ / p| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    linarith
  rw [coordinateRemainder_eq hp.ne', abs_mul, abs_of_pos hp]
  calc
    _ ≤ p * (4 * |δ / p| ^ 3) := mul_le_mul_of_nonneg_left
      (abs_entropyRemainder_le hu) hp.le
    _ = _ := by rw [abs_div, abs_of_pos hp]; field_simp

/-- The scaled multinomial entropy exponent differs from its Gaussian
quadratic exponent by an explicit `N⁻¹ᐟ²` bound. -/
theorem central_entropy_bound {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (n a R : ℝ) (hn : 0 < n) (ha : 0 < a) (hR : 0 ≤ R)
    (hp : ∀ i, a ≤ p i) (hx : ∀ i, |x i| ≤ R)
    (hsmall : R / Real.sqrt n ≤ a / 2) (hzero : ∑ i, x i = 0) :
    |n * (∑ i, (p i + x i / Real.sqrt n) *
        Real.log ((p i + x i / Real.sqrt n) / p i)) -
      (∑ i, (x i) ^ 2 / (2 * p i))| ≤
      4 * Fintype.card ι * R ^ 3 / (a ^ 2 * Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hp0 i : 0 < p i := ha.trans_le (hp i)
  have hb i : |x i / Real.sqrt n| ≤ p i / 2 := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_div_of_nonneg_right (hx i) hs.le).trans
      (hsmall.trans (div_le_div_of_nonneg_right (hp i) (by norm_num)))
  have hquad : n * (∑ i, (x i / Real.sqrt n) ^ 2 / (2 * p i)) =
      ∑ i, (x i) ^ 2 / (2 * p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, hs2]
    field_simp
  have heq : n * (∑ i, (p i + x i / Real.sqrt n) *
        Real.log ((p i + x i / Real.sqrt n) / p i)) -
      (∑ i, (x i) ^ 2 / (2 * p i)) =
      n * ∑ i, coordinateRemainder (p i) (x i / Real.sqrt n) := by
    simp only [coordinateRemainder, Finset.sum_sub_distrib, div_eq_mul_inv, ← Finset.sum_mul, hzero,
      zero_mul, sub_zero, mul_sub]
    simpa only [div_eq_mul_inv] using congrArg
      (fun z ↦ n * (∑ i, (p i + x i / Real.sqrt n) *
        Real.log ((p i + x i / Real.sqrt n) / p i)) - z) hquad.symm
  rw [heq, abs_mul, abs_of_pos hn]
  calc
    _ ≤ n * ∑ i, |coordinateRemainder (p i) (x i / Real.sqrt n)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ n * ∑ _i : ι, 4 * R ^ 3 / (a ^ 2 * Real.sqrt n ^ 3) := by
      gcongr with i
      refine (abs_coordinateRemainder_le (hp0 i) (hb i)).trans ?_
      rw [abs_div, abs_of_pos hs, div_pow]
      calc
        4 * (|x i| ^ 3 / Real.sqrt n ^ 3) / p i ^ 2 ≤
            4 * (R ^ 3 / Real.sqrt n ^ 3) / a ^ 2 := by gcongr; exact hx i; exact hp i
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      rw [hs2]
      ring

end Cloning.YoungMultinomial
