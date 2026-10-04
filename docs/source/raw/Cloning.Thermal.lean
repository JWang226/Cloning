import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Thermal scalar calculations from `cloning.tex`

These are statements about geometric probability distributions and real scalar
formulas.  Identification with diagonal quantum states is not claimed here.
-/

noncomputable section

namespace Cloning.Thermal

/-- Number probabilities of a one-mode thermal state. -/
def geometric (q : ℝ) (n : ℕ) : ℝ := (1 - q) * q ^ n

/-- Root fidelity of two geometric distributions in closed form. -/
def fidelity (q x : ℝ) : ℝ :=
  Real.sqrt ((1 - q) * (1 - x)) / (1 - Real.sqrt (q * x))

/-- Thermal parameter after quantum-limited amplification. -/
def amplified (g q : ℝ) : ℝ := 1 - (1 - q) / g

/-- Thermal parameter in the purify-clone-trace limit. -/
def pct (g q : ℝ) : ℝ := (g - 1 + g * q) / (g + (g - 1) * q)

/-- Mean photon number of a geometric distribution. -/
def photonMean (q : ℝ) : ℝ := q / (1 - q)

theorem geometric_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    0 ≤ geometric q n := mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq0 n)

theorem geometric_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (geometric q) 1 := by
  simpa [geometric, ne_of_gt (sub_pos.mpr hq1)] using
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - q)

theorem sqrt_nat_pow {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    Real.sqrt (q ^ n) = Real.sqrt q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hq n), ih, pow_succ]

theorem affinity_term {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    Real.sqrt (geometric q n * geometric x n) =
      Real.sqrt ((1 - q) * (1 - x)) * Real.sqrt (q * x) ^ n := by
  have he : geometric q n * geometric x n = (1 - q) * (1 - x) * (q * x) ^ n := by
    simp only [geometric, mul_pow]
    ring
  rw [he, Real.sqrt_mul (mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hx1.le)), sqrt_nat_pow (mul_nonneg hq0 hx0)]

theorem affinity_hasSum {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n => Real.sqrt (geometric q n * geometric x n)) (fidelity q x) := by
  have hqx : q * x < 1 := mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx0 hx1
  have hs : Real.sqrt (q * x) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using hqx
  simp_rw [affinity_term hq0 hq1 hx0 hx1]
  simpa [fidelity, div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one (Real.sqrt_nonneg _) hs).mul_left
      (Real.sqrt ((1 - q) * (1 - x)))

theorem affinity_tsum {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' n, Real.sqrt (geometric q n * geometric x n)) = fidelity q x :=
  (affinity_hasSum hq0 hq1 hx0 hx1).tsum_eq

theorem fidelity_pos {q x : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 < fidelity q x := by
  have hqx : q * x < 1 := mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx0 hx1
  have hs : Real.sqrt (q * x) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using hqx
  unfold fidelity
  exact div_pos (Real.sqrt_pos.2 (mul_pos (sub_pos.mpr hq1) (sub_pos.mpr hx1)))
    (sub_pos.mpr hs)

theorem fidelity_sq {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    fidelity q x ^ 2 = (1 - q) * (1 - x) / (1 - Real.sqrt q * Real.sqrt x) ^ 2 := by
  unfold fidelity
  rw [div_pow, Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hx1.le)), Real.sqrt_mul hq0]

theorem fidelity_le_one {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : fidelity q x ≤ 1 := by
  have hprod : q * x < 1 := mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx0 hx1
  have hsqrt : Real.sqrt q * Real.sqrt x < 1 := by
    rw [← Real.sqrt_mul hq0, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using hprod
  have hsq : (Real.sqrt q * Real.sqrt x) ^ 2 = q * x := by
    rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hx0]
  have hnum : (1 - q) * (1 - x) ≤ (1 - Real.sqrt q * Real.sqrt x) ^ 2 := by
    nlinarith [Real.sq_sqrt hq0, Real.sq_sqrt hx0,
      sq_nonneg (Real.sqrt q - Real.sqrt x)]
  have hf : fidelity q x ^ 2 ≤ 1 := by
    rw [fidelity_sq hq0 hq1 hx0 hx1]
    exact (div_le_one (sq_pos_of_pos (sub_pos.mpr hsqrt))).mpr hnum
  nlinarith

/-- Algebra behind strict decrease of thermal fidelity beyond its maximum. -/
theorem fidelity_sq_strict_aux {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hbc : b < c) (hc : c < 1) :
    (1 - a ^ 2) * (1 - c ^ 2) / (1 - a * c) ^ 2 <
      (1 - a ^ 2) * (1 - b ^ 2) / (1 - a * b) ^ 2 := by
  have hb : 0 ≤ b := le_trans ha hab.le
  have hc0 : 0 ≤ c := le_trans hb hbc.le
  have ha1 : a < 1 := lt_trans hab (lt_trans hbc hc)
  have hab1 : a * b < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha1.le hb (lt_trans hbc hc)
  have hac1 : a * c < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha1.le hc0 hc
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  apply (div_lt_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hac1))
    (sq_pos_of_pos (sub_pos.mpr hab1))).mpr
  have hid :
      (1 - a ^ 2) * (1 - b ^ 2) * (1 - a * c) ^ 2 -
        (1 - a ^ 2) * (1 - c ^ 2) * (1 - a * b) ^ 2 =
      (1 - a ^ 2) * (c - b) *
        ((b - a) * (1 - a * c) + (c - a) * (1 - a * b)) := by ring
  have hp : 0 < (1 - a ^ 2) * (c - b) *
      ((b - a) * (1 - a * c) + (c - a) * (1 - a * b)) := by
    apply mul_pos (mul_pos ha2 (sub_pos.mpr hbc))
    exact add_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hac1))
      (mul_pos (sub_pos.mpr (lt_trans hab hbc)) (sub_pos.mpr hab1))
  linarith

theorem fidelity_strictAnti_right {q x y : ℝ} (hq0 : 0 ≤ q)
    (hqx : q < x) (hxy : x < y) (hy1 : y < 1) :
    fidelity q y < fidelity q x := by
  have hx0 : 0 ≤ x := le_trans hq0 hqx.le
  have hy0 : 0 ≤ y := le_trans hx0 hxy.le
  have hx1 : x < 1 := lt_trans hxy hy1
  have hq1 : q < 1 := lt_trans hqx hx1
  have hs := fidelity_sq_strict_aux (Real.sqrt_nonneg q)
    (Real.sqrt_lt_sqrt hq0 hqx) (Real.sqrt_lt_sqrt hx0 hxy)
    (show Real.sqrt y < 1 by rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]; simpa)
  rw [Real.sq_sqrt hq0, Real.sq_sqrt hx0, Real.sq_sqrt hy0] at hs
  rw [← fidelity_sq hq0 hq1 hy0 hy1, ← fidelity_sq hq0 hq1 hx0 hx1] at hs
  have hp := fidelity_pos hq0 hq1 hy0 hy1
  have hp' := fidelity_pos hq0 hq1 hx0 hx1
  nlinarith

theorem amplified_eq {g q : ℝ} (hg : g ≠ 0) :
    amplified g q = (g - 1 + q) / g := by
  unfold amplified
  field_simp
  ring

theorem lt_amplified {g q : ℝ} (hg : 1 < g) (hq : q < 1) :
    q < amplified g q := by
  rw [amplified_eq (by linarith)]
  apply (lt_div_iff₀ (by linarith : 0 < g)).mpr
  nlinarith [mul_pos (by linarith : 0 < g - 1) (by linarith : 0 < 1 - q)]

theorem amplified_lt_one {g q : ℝ} (hg : 0 < g) (hq : q < 1) :
    amplified g q < 1 := by
  unfold amplified
  have := div_pos (sub_pos.mpr hq) hg
  linarith

theorem amplified_nonneg {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ amplified g q := le_trans hq0 (lt_amplified hg hq1).le

theorem pct_denominator_pos {g q : ℝ} (hg : 1 < g) (hq : 0 ≤ q) :
    0 < g + (g - 1) * q :=
  add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg (by linarith) hq)

theorem amplified_lt_pct {g q : ℝ} (hg : 1 < g) (hq0 : 0 < q) (hq1 : q < 1) :
    amplified g q < pct g q := by
  rw [amplified_eq (by linarith)]
  unfold pct
  apply (div_lt_div_iff₀ (by linarith : 0 < g) (pct_denominator_pos hg hq0.le)).mpr
  have h := mul_pos (mul_pos (by linarith : 0 < g - 1) hq0) (sub_pos.mpr hq1)
  nlinarith

theorem pct_lt_one {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    pct g q < 1 := by
  unfold pct
  rw [div_lt_one (pct_denominator_pos hg hq0)]
  nlinarith

theorem amplified_photonMean {g q : ℝ} (hg : 0 < g) (hq : q < 1) :
    photonMean (amplified g q) = g * q / (1 - q) + g - 1 := by
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hq0 : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  unfold photonMean amplified
  field_simp [hg0, hq0]
  ring

theorem pct_photonMean {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    photonMean (pct g q) = (g - 1 + g * q) / (1 - q) := by
  have hd := ne_of_gt (pct_denominator_pos hg hq0)
  have hq := ne_of_gt (sub_pos.mpr hq1)
  unfold photonMean
  apply (div_eq_iff (ne_of_gt (sub_pos.mpr (pct_lt_one hg hq0 hq1)))).mpr
  unfold pct
  field_simp [hd, hq]
  ring

theorem pct_excess_photonMean {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    photonMean (pct g q) - photonMean (amplified g q) =
      (g - 1) * q / (1 - q) := by
  rw [pct_photonMean hg hq0 hq1, amplified_photonMean (by linarith) hq1]
  field_simp [ne_of_gt (sub_pos.mpr hq1)]
  ring

theorem pct_fidelity_lt_amplified {g q : ℝ} (hg : 1 < g) (hq0 : 0 < q)
    (hq1 : q < 1) : fidelity q (pct g q) < fidelity q (amplified g q) :=
  fidelity_strictAnti_right hq0.le (lt_amplified hg hq1)
    (amplified_lt_pct hg hq0 hq1) (pct_lt_one hg hq0.le hq1)

/-- The manuscript's rationalized one-mode factor `f_γ(q)`. -/
def modeFactor (g q : ℝ) : ℝ :=
  (Real.sqrt g + Real.sqrt (q * (g - 1 + q))) / (g + q)

theorem fidelity_amplified_unrationalized {g q : ℝ} (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    fidelity q (amplified g q) =
      (1 - q) / (Real.sqrt g - Real.sqrt (q * (g - 1 + q))) := by
  have hg0 : g ≠ 0 := by linarith
  have hs : Real.sqrt g ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have ht : 0 ≤ 1 - q := sub_nonneg.mpr hq1.le
  have hn : Real.sqrt ((1 - q) * (1 - amplified g q)) = (1 - q) / Real.sqrt g := by
    have he : (1 - q) * (1 - amplified g q) = (1 - q) ^ 2 / g := by
      unfold amplified
      ring
    rw [he, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq ht]
  have hr : Real.sqrt (q * amplified g q) =
      Real.sqrt (q * (g - 1 + q)) / Real.sqrt g := by
    rw [amplified_eq hg0, ← mul_div_assoc,
      Real.sqrt_div (mul_nonneg hq0 (by linarith))]
  unfold fidelity
  rw [hn, hr]
  field_simp [hs]

theorem fidelity_amplified_eq_modeFactor {g q : ℝ} (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    fidelity q (amplified g q) = modeFactor g q := by
  have hg0 : 0 < g := by linarith
  have hsum : 0 < g + q := by linarith
  have hrad : 0 ≤ q * (g - 1 + q) := mul_nonneg hq0 (by linarith)
  have hradlt : q * (g - 1 + q) < g := by
    have hp := mul_pos (sub_pos.mpr hq1) hsum
    nlinarith
  have hd : 0 < Real.sqrt g - Real.sqrt (q * (g - 1 + q)) :=
    sub_pos.mpr (Real.sqrt_lt_sqrt hrad hradlt)
  rw [fidelity_amplified_unrationalized hg hq0 hq1]
  unfold modeFactor
  apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hsum)).mpr
  nlinarith [Real.sq_sqrt hg0.le, Real.sq_sqrt hrad]

theorem modeFactor_pos {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < modeFactor g q := by
  rw [← fidelity_amplified_eq_modeFactor hg hq0 hq1]
  exact fidelity_pos hq0 hq1 (amplified_nonneg hg hq0 hq1)
    (amplified_lt_one (by linarith) hq1)

theorem modeFactor_le_one {g q : ℝ} (hg : 1 < g) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    modeFactor g q ≤ 1 := by
  rw [← fidelity_amplified_eq_modeFactor hg hq0 hq1]
  exact fidelity_le_one hq0 hq1 (amplified_nonneg hg hq0 hq1)
    (amplified_lt_one (by linarith) hq1)

theorem modeFactor_continuousAt {g q : ℝ} (hden : g + q ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => modeFactor z.1 z.2) (g, q) := by
  unfold modeFactor
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact hden

theorem pct_fidelity_lt_modeFactor {g q : ℝ} (hg : 1 < g) (hq0 : 0 < q)
    (hq1 : q < 1) : fidelity q (pct g q) < modeFactor g q := by
  rw [← fidelity_amplified_eq_modeFactor hg hq0.le hq1]
  exact pct_fidelity_lt_amplified hg hq0 hq1

/-- Base of the equal-mean Gaussian Hellinger affinity. -/
def classicalBase (c : ℝ) : ℝ := 2 * Real.sqrt c / (1 + c)

theorem classicalBase_pos {c : ℝ} (hc : 0 < c) : 0 < classicalBase c := by
  unfold classicalBase
  positivity

theorem classicalBase_le_one {c : ℝ} (hc : 0 ≤ c) : classicalBase c ≤ 1 := by
  unfold classicalBase
  apply (div_le_one (by linarith : 0 < 1 + c)).mpr
  nlinarith [Real.sq_sqrt hc, sq_nonneg (Real.sqrt c - 1)]

theorem classicalBase_lt_one {c : ℝ} (hc : 1 < c) : classicalBase c < 1 := by
  have hc0 : 0 ≤ c := by linarith
  have hs : 1 < Real.sqrt c := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hc
  unfold classicalBase
  apply (div_lt_one (by linarith : 0 < 1 + c)).mpr
  nlinarith [Real.sq_sqrt hc0, sq_pos_of_pos (sub_pos.mpr hs)]

theorem classicalBase_strictAnti {x y : ℝ} (hx : 1 < x) (hxy : x < y) :
    classicalBase y < classicalBase x := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have ha : 1 < Real.sqrt x := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx
  have hab : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx0 hxy
  have hp : 0 < (Real.sqrt y - Real.sqrt x) * (Real.sqrt x * Real.sqrt y - 1) := by
    apply mul_pos (sub_pos.mpr hab)
    nlinarith
  unfold classicalBase
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + y) (by linarith : 0 < 1 + x)).mpr
  nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt hy0]

theorem pct_classicalBase_lt {g : ℝ} (hg : 1 < g) :
    classicalBase (2 * g - 1) < classicalBase g :=
  classicalBase_strictAnti hg (by linarith)

/-- Eigenvalues of the diagonal fidelity witness. -/
def witness (q x : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (geometric q n) / Real.sqrt (geometric x n)

theorem geometric_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < geometric q n := mul_pos (sub_pos.mpr hq1) (pow_pos hq0 n)

theorem witness_pos {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) : 0 < witness q x n :=
  div_pos (Real.sqrt_pos.2 (geometric_pos hq0 hq1 n))
    (Real.sqrt_pos.2 (geometric_pos hx0 hx1 n))

theorem witness_closed {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    witness q x n = Real.sqrt ((1 - q) / (1 - x)) * Real.sqrt (q / x) ^ n := by
  unfold witness geometric
  rw [Real.sqrt_mul (sub_nonneg.mpr hq1.le), Real.sqrt_mul (sub_nonneg.mpr hx1.le),
    sqrt_nat_pow hq0, sqrt_nat_pow hx0, Real.sqrt_div (sub_nonneg.mpr hq1.le),
    Real.sqrt_div hq0, div_pow]
  ring

theorem witness_strictAnti {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    StrictAnti (witness q x) := by
  have hx0 : 0 < x := lt_trans hq0 hqx
  have hq1 : q < 1 := lt_trans hqx hx1
  have hr0 : 0 < Real.sqrt (q / x) := Real.sqrt_pos.2 (div_pos hq0 hx0)
  have hr1 : Real.sqrt (q / x) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using (div_lt_one hx0).mpr hqx
  intro m n hmn
  rw [witness_closed hq0.le hq1 hx0.le hx1, witness_closed hq0.le hq1 hx0.le hx1]
  apply mul_lt_mul_of_pos_left (pow_right_strictAnti₀ hr0 hr1 hmn)
  exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hq1) (sub_pos.mpr hx1))

theorem witness_bounded {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1)
    (n : ℕ) : witness q x n ≤ Real.sqrt ((1 - q) / (1 - x)) := by
  have h := (witness_strictAnti hq0 hqx hx1).antitone (Nat.zero_le n)
  simpa [witness_closed hq0.le (lt_trans hqx hx1) (lt_trans hq0 hqx).le hx1] using h

theorem witness_tendsto_zero {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    Filter.Tendsto (witness q x) Filter.atTop (nhds 0) := by
  have hx0 : 0 < x := lt_trans hq0 hqx
  have hq1 : q < 1 := lt_trans hqx hx1
  have hr1 : Real.sqrt (q / x) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using (div_lt_one hx0).mpr hqx
  have he : witness q x =
      fun n => Real.sqrt ((1 - q) / (1 - x)) * Real.sqrt (q / x) ^ n := by
    funext n
    exact witness_closed hq0.le hq1 hx0.le hx1 n
  rw [he]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg (q / x)) hr1).const_mul
    (Real.sqrt ((1 - q) / (1 - x)))

theorem witness_weighted_term {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    geometric x n * witness q x n = Real.sqrt (geometric q n * geometric x n) := by
  have hp := geometric_pos hx0 hx1 n
  have hs : Real.sqrt (geometric x n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  unfold witness
  rw [Real.sqrt_mul (geometric_nonneg hq0 hq1.le n)]
  rw [← mul_div_assoc]
  apply (div_eq_iff hs).mpr
  calc
    geometric x n * Real.sqrt (geometric q n) =
        Real.sqrt (geometric x n) ^ 2 * Real.sqrt (geometric q n) := by
      rw [Real.sq_sqrt hp.le]
    _ = _ := by ring

theorem witness_inverse_term {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (_hx0 : 0 < x) (_hx1 : x < 1) (n : ℕ) :
    geometric q n / witness q x n = Real.sqrt (geometric q n * geometric x n) := by
  have hp := geometric_pos hq0 hq1 n
  have hs : Real.sqrt (geometric q n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  unfold witness
  rw [Real.sqrt_mul hp.le, div_div_eq_mul_div]
  apply (div_eq_iff hs).mpr
  calc
    geometric q n * Real.sqrt (geometric x n) =
        Real.sqrt (geometric q n) ^ 2 * Real.sqrt (geometric x n) := by
      rw [Real.sq_sqrt hp.le]
    _ = _ := by ring

theorem witness_moment_hasSum {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n => geometric x n * witness q x n) (fidelity q x) := by
  simp_rw [witness_weighted_term hq0.le hq1 hx0 hx1]
  exact affinity_hasSum hq0.le hq1 hx0.le hx1

theorem witness_inverse_moment_hasSum {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n => geometric q n / witness q x n) (fidelity q x) := by
  simp_rw [witness_inverse_term hq0 hq1 hx0 hx1]
  exact affinity_hasSum hq0.le hq1 hx0.le hx1

/-- An absolutely convergent product-distribution identity, including zero modes. -/
theorem hasSum_fin_product (s : ℕ) (f : Fin s → ℕ → ℝ) (a : Fin s → ℝ)
    (hn : ∀ i n, 0 ≤ f i n) (hs : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun k : Fin s → ℕ => ∏ i, f i (k i)) (∏ i, a i) := by
  induction s with
  | zero =>
    simpa using hasSum_fintype (fun k : Fin 0 → ℕ => ∏ i, f i (k i))
  | succ s ih =>
    have ht : HasSum (fun k : Fin s → ℕ => ∏ i : Fin s, f i.succ (k i))
        (∏ i : Fin s, a i.succ) := ih (fun i => f i.succ) (fun i => a i.succ)
      (fun i n => hn i.succ n) (fun i => hs i.succ)
    have hn' : ∀ k : Fin s → ℕ, 0 ≤ ∏ i : Fin s, f i.succ (k i) :=
      fun k => Finset.prod_nonneg (fun i _ => hn i.succ (k i))
    have hsum : Summable (fun k : ℕ × (Fin s → ℕ) =>
        f 0 k.1 * ∏ i : Fin s, f i.succ (k.2 i)) := by
      apply (summable_prod_of_nonneg (fun k => mul_nonneg (hn 0 k.1) (hn' k.2))).mpr
      constructor
      · intro n
        exact ht.summable.mul_left (f 0 n)
      · have he : (fun n : ℕ => ∑' k : Fin s → ℕ, f 0 n * ∏ i : Fin s, f i.succ (k i)) =
            fun n => f 0 n * ∏ i : Fin s, a i.succ := by
          funext n
          rw [tsum_mul_left, ht.tsum_eq]
        rw [he]
        exact (hs 0).summable.mul_right (∏ i : Fin s, a i.succ)
    have hm : HasSum (fun k : ℕ × (Fin s → ℕ) =>
        f 0 k.1 * ∏ i : Fin s, f i.succ (k.2 i)) (a 0 * ∏ i : Fin s, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun k : Fin s → ℕ => ∏ i : Fin s, f i.succ (k i))
        (s := a 0) (t := ∏ i : Fin s, a i.succ) (hs 0) ht hsum
    rw [← (Fin.consEquiv (fun _ : Fin (s + 1) => ℕ)).hasSum_iff]
    simpa [Fin.prod_univ_succ, Fin.consEquiv, Function.comp_def] using hm

/-- The product geometric law is a probability distribution. -/
theorem multimode_geometric_hasSum {s : ℕ} {q : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HasSum (fun k : Fin s → ℕ => ∏ i, geometric (q i) (k i)) 1 := by
  simpa using hasSum_fin_product s (fun i => geometric (q i)) (fun _ => 1)
    (fun i n => geometric_nonneg (hq0 i) (hq1 i).le n)
    (fun i => geometric_hasSum (hq0 i) (hq1 i))

/-- Multiplicativity of thermal affinity, as a convergent series over number tuples. -/
theorem multimode_affinity_hasSum {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    HasSum (fun k : Fin s → ℕ =>
      ∏ i, Real.sqrt (geometric (q i) (k i) * geometric (x i) (k i)))
      (∏ i, fidelity (q i) (x i)) :=
  hasSum_fin_product s
    (fun i n => Real.sqrt (geometric (q i) n * geometric (x i) n))
    (fun i => fidelity (q i) (x i)) (fun _ _ => Real.sqrt_nonneg _)
    (fun i => affinity_hasSum (hq0 i) (hq1 i) (hx0 i) (hx1 i))

theorem multimode_affinity_of_product_laws {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    HasSum (fun k : Fin s → ℕ => Real.sqrt
      ((∏ i, geometric (q i) (k i)) * (∏ i, geometric (x i) (k i))))
      (∏ i, fidelity (q i) (x i)) := by
  have he : (fun k : Fin s → ℕ => Real.sqrt
      ((∏ i, geometric (q i) (k i)) * (∏ i, geometric (x i) (k i)))) =
      fun k => ∏ i, Real.sqrt (geometric (q i) (k i) * geometric (x i) (k i)) := by
    funext k
    rw [← Finset.prod_mul_distrib]
    exact Real.sqrt_prod _ (fun i _ => mul_nonneg
      (geometric_nonneg (hq0 i) (hq1 i).le (k i))
      (geometric_nonneg (hx0 i) (hx1 i).le (k i)))
  rw [he]
  exact multimode_affinity_hasSum hq0 hq1 hx0 hx1

/-- A common geometric envelope controls the witness by total occupation. -/
theorem multimode_witness_envelope {s : ℕ} {q x : Fin s → ℝ} {r : ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (hr : ∀ i, Real.sqrt (q i / x i) ≤ r) (k : Fin s → ℕ) :
    (∏ i, witness (q i) (x i) (k i)) ≤
      (∏ i, Real.sqrt ((1 - q i) / (1 - x i))) * r ^ (∑ i, k i) := by
  calc
    (∏ i, witness (q i) (x i) (k i)) ≤
        ∏ i, Real.sqrt ((1 - q i) / (1 - x i)) * r ^ k i := by
      apply Finset.prod_le_prod
      · intro i _
        exact (witness_pos (hq0 i) (lt_trans (hqx i) (hx1 i))
          (lt_trans (hq0 i) (hqx i)) (hx1 i) (k i)).le
      · intro i _
        rw [witness_closed (hq0 i).le (lt_trans (hqx i) (hx1 i))
          (lt_trans (hq0 i) (hqx i)).le (hx1 i)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hr i) (k i)) (Real.sqrt_nonneg _)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Along any family escaping in total occupation, a common ratio bound gives
the vanishing-eigenvalue conclusion needed for compactness of the witness. -/
theorem multimode_witness_tendsto_zero {s : ℕ} {q x : Fin s → ℝ} {r : ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : ∀ i, Real.sqrt (q i / x i) ≤ r)
    (k : ℕ → Fin s → ℕ)
    (hk : Filter.Tendsto (fun n => ∑ i, k n i) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => ∏ i, witness (q i) (x i) (k n i)) Filter.atTop (nhds 0) := by
  have he := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hk
  have hb : Filter.Tendsto
      (fun n => (∏ i, Real.sqrt ((1 - q i) / (1 - x i))) * r ^ (∑ i, k n i))
      Filter.atTop (nhds 0) := by
    simpa using he.const_mul (∏ i, Real.sqrt ((1 - q i) / (1 - x i)))
  apply squeeze_zero
    (fun n => Finset.prod_nonneg (fun i _ =>
      (witness_pos (hq0 i) (lt_trans (hqx i) (hx1 i))
        (lt_trans (hq0 i) (hqx i)) (hx1 i) (k n i)).le))
    (fun n => multimode_witness_envelope hq0 hqx hx1 hr (k n)) hb

/-- The witness moment identity for any finite number of oscillator modes. -/
theorem multimode_witness_moment_hasSum {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1) :
    HasSum (fun k : Fin s → ℕ =>
      ∏ i, geometric (x i) (k i) * witness (q i) (x i) (k i))
      (∏ i, fidelity (q i) (x i)) := by
  simp_rw [witness_weighted_term (hq0 _).le (hq1 _) (hx0 _) (hx1 _)]
  exact multimode_affinity_hasSum (fun i => (hq0 i).le) hq1 (fun i => (hx0 i).le) hx1

end Cloning.Thermal
