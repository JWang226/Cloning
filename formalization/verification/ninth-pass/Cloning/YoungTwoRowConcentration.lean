import Cloning.YoungTwoRowAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exponential concentration and reciprocal Weyl moments for two rows

The concrete tableau-path law is bounded by `(N+1)` times the fair binary
path law. An exact generating-function calculation proves a fixed-fraction
tail bound `(N+1)(9/10)^N`, without any concentration hypothesis.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungTwoRow
open YoungDimensionRatio

/-- The unnormalized exponential moment of the actual upper-row count. -/
theorem sum_four_pow_upperRow (N : ℕ) :
    (∑ p : Path N, (4 : ℝ) ^ upperRow N p) = 5 ^ N := by
  induction N with
  | zero => simp [Path, upperRow]
  | succ N ih =>
    change (∑ p : Path N × Bool, (4 : ℝ) ^ upperRow (N + 1) p) = _
    rw [Fintype.sum_prod_type]
    have hp (p : Path N) : (∑ b : Bool, (4 : ℝ) ^ upperRow (N + 1) (p, b)) =
        5 * 4 ^ upperRow N p := by
      simp [upperRow, pow_succ]
      ring
    simp_rw [hp]
    rw [← Finset.mul_sum, ih, pow_succ]
    ring

/-- Every legal path has Schur weight at most `(N+1)` times its fair-walk weight. -/
theorem weight_le_uniform_factor (N : ℕ) (p : Path N) :
    weight N p ≤ ((N : ℝ) + 1) / (2 : ℝ) ^ N := by
  rw [weight_formula]
  split_ifs
  · apply div_le_div_of_nonneg_right _ (pow_nonneg (by norm_num) _)
    exact_mod_cast Nat.succ_le_succ (spin_le_length N p)
  · positivity

/-- The actual probability of a row gap larger than half the sample size. -/
def largeGapProbability (N : ℕ) : ℝ :=
  ∑ p : Path N, if N < 2 * spin N p then weight N p else 0

theorem largeGapProbability_nonneg (N : ℕ) : 0 ≤ largeGapProbability N := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact weight_nonneg N p
  · exact le_rfl

private theorem sqrt_eight_pow_le (N : ℕ) (p : Path N) (hp : legal N p)
    (htail : N < 2 * spin N p) :
    Real.sqrt 8 ^ N ≤ (4 : ℝ) ^ upperRow N p := by
  have hsum := row_sum N p
  have hgap := spin_add_lower_eq_upper N p hp
  have hexp : 3 * N ≤ 4 * upperRow N p := by omega
  have hpow : (8 : ℝ) ^ N ≤ (16 : ℝ) ^ upperRow N p := by
    calc
      _ = (2 : ℝ) ^ (3 * N) := by rw [pow_mul]; norm_num
      _ ≤ (2 : ℝ) ^ (4 * upperRow N p) := pow_le_pow_right₀ (by norm_num) hexp
      _ = _ := by rw [pow_mul]; norm_num
  have hs : (Real.sqrt 8) ^ 2 = (8 : ℝ) := Real.sq_sqrt (by norm_num)
  have hl : (Real.sqrt 8 ^ N) ^ 2 = (8 : ℝ) ^ N := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul, hs]
  have hr : ((4 : ℝ) ^ upperRow N p) ^ 2 = (16 : ℝ) ^ upperRow N p := by
    rw [← pow_mul, Nat.mul_comm (upperRow N p) 2, pow_mul]
    norm_num
  apply (sq_le_sq₀ (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg (by norm_num) _)).mp
  rwa [hl, hr]

/-- A genuine exponential tail bound for the concrete Schur path law. -/
theorem largeGapProbability_le (N : ℕ) :
    largeGapProbability N ≤ ((N : ℝ) + 1) * (9 / 10 : ℝ) ^ N := by
  have hs0 : 0 < Real.sqrt (8 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hpoint (p : Path N) :
      (if N < 2 * spin N p then weight N p else 0) ≤
        (((N : ℝ) + 1) / ((2 : ℝ) ^ N * Real.sqrt 8 ^ N)) * 4 ^ upperRow N p := by
    by_cases ht : N < 2 * spin N p
    · rw [if_pos ht]
      by_cases hp : legal N p
      · have hratio : (1 : ℝ) ≤ 4 ^ upperRow N p / Real.sqrt 8 ^ N :=
          (one_le_div (pow_pos hs0 N)).mpr (sqrt_eight_pow_le N p hp ht)
        calc
          _ ≤ ((N : ℝ) + 1) / (2 : ℝ) ^ N := weight_le_uniform_factor N p
          _ ≤ (((N : ℝ) + 1) / (2 : ℝ) ^ N) *
              (4 ^ upperRow N p / Real.sqrt 8 ^ N) :=
            le_mul_of_one_le_right (by positivity) hratio
          _ = _ := by ring
      · rw [weight_eq_zero_of_not_legal N p hp]
        positivity
    · rw [if_neg ht]
      positivity
  have hq0 : (0 : ℝ) ≤ 5 / (2 * Real.sqrt 8) := by positivity
  have hq : (5 : ℝ) / (2 * Real.sqrt 8) ≤ 9 / 10 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hs0)).mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)]
  calc
    _ ≤ ∑ p : Path N,
        (((N : ℝ) + 1) / ((2 : ℝ) ^ N * Real.sqrt 8 ^ N)) * 4 ^ upperRow N p :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = ((N : ℝ) + 1) * (5 / (2 * Real.sqrt 8)) ^ N := by
      rw [← Finset.mul_sum, sum_four_pow_upperRow, div_pow, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq N) (by positivity)

theorem dimensionRatio_ge_one (k N : ℕ) (p : Path N) :
    1 ≤ dimensionRatio 2 k (rowVector N p) := by
  apply Finset.one_le_prod
  intro a ha
  apply (one_le_div (crossingGap_pos a)).mpr
  exact le_add_of_nonneg_left (rowVector_bounds N p a.1).1

/-- Central legal shapes have both rows at least `N/4`. -/
theorem rowVector_lower_of_small_gap (N : ℕ) (p : Path N) (hp : legal N p)
    (hgap : 2 * spin N p ≤ N) (i : Fin 2) : (N : ℝ) / 4 ≤ rowVector N p i := by
  have hs : (upperRow N p : ℝ) + (lowerRow N p : ℝ) = N := by exact_mod_cast row_sum N p
  have hg : (spin N p : ℝ) + (lowerRow N p : ℝ) = upperRow N p :=
    by exact_mod_cast spin_add_lower_eq_upper N p hp
  have ht : 2 * (spin N p : ℝ) ≤ N := by exact_mod_cast hgap
  have hsp : 0 ≤ (spin N p : ℝ) := Nat.cast_nonneg _
  dsimp [rowVector]
  split_ifs <;> linarith

theorem normalized_dimensionRatio_lower (k N : ℕ) (hN : 1 ≤ N)
    (p : Path N) (hp : legal N p) (hgap : 2 * spin N p ≤ N) :
    (1 / 2 : ℝ) ^ (2 * k) ≤ dimensionRatio 2 k (rowVector N p) /
      (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hden : leadingConstant 2 k * (N : ℝ) ^ (2 * k) ≠ 0 :=
    (mul_pos (leadingConstant_pos 2 k (by decide)) (pow_pos hN0 _)).ne'
  rw [dimensionRatio_factorization 2 k (rowVector N p) N (by decide) hN0,
    mul_div_cancel_left₀ _ hden]
  have hf (a : Fin 2 × Fin k) : (1 / 2 : ℝ) ≤
      (2 : ℝ) * (rowVector N p a.1 + crossingGap a) / N := by
    apply (le_div_iff₀ hN0).mpr
    have := rowVector_lower_of_small_gap N p hp hgap a.1
    have := (crossingGap_pos a).le
    linarith
  calc
    _ = ∏ _a : Fin 2 × Fin k, (1 / 2 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun a _ => hf a)

theorem inverse_normalized_dimensionRatio_upper (k N : ℕ) (hN : 1 ≤ N)
    (p : Path N) (hp : legal N p) (hgap : 2 * spin N p ≤ N) :
    (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) /
      dimensionRatio 2 k (rowVector N p) ≤ (2 : ℝ) ^ (2 * k) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hden : 0 < leadingConstant 2 k * (N : ℝ) ^ (2 * k) :=
    mul_pos (leadingConstant_pos 2 k (by decide)) (pow_pos hN0 _)
  have hR : 0 < dimensionRatio 2 k (rowVector N p) :=
    lt_of_lt_of_le zero_lt_one (dimensionRatio_ge_one k N p)
  apply (div_le_iff₀ hR).mpr
  have hl := (le_div_iff₀ hden).mp (normalized_dimensionRatio_lower k N hN p hp hgap)
  have hid : (2 : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ (2 * k) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (2 : ℝ) ^ (2 * k) * ((1 / 2 : ℝ) ^ (2 * k) *
        (leadingConstant 2 k * (N : ℝ) ^ (2 * k))) := by rw [← mul_assoc, hid, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (pow_nonneg (by norm_num) _)

theorem reciprocal_error_of_small_gap (k N : ℕ) (hN : 1 ≤ N)
    (p : Path N) (hp : legal N p) (hgap : 2 * spin N p ≤ N) :
    |(leadingConstant 2 k * (N : ℝ) ^ (2 * k)) /
      dimensionRatio 2 k (rowVector N p) - 1| ≤
      (2 : ℝ) ^ (2 * k) * |dimensionRatio 2 k (rowVector N p) /
        (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1| := by
  let R := dimensionRatio 2 k (rowVector N p)
  let D := leadingConstant 2 k * (N : ℝ) ^ (2 * k)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hD : 0 < D := mul_pos (leadingConstant_pos 2 k (by decide)) (pow_pos hN0 _)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (dimensionRatio_ge_one k N p)
  have heq : D / R - 1 = -(D / R) * (R / D - 1) := by field_simp; ring
  change |D / R - 1| ≤ 2 ^ (2 * k) * |R / D - 1|
  rw [heq, abs_mul, abs_neg, abs_of_pos (div_pos hD hR)]
  exact mul_le_mul_of_nonneg_right (inverse_normalized_dimensionRatio_upper k N hN p hp hgap)
    (abs_nonneg _)

/-- The reciprocal error is at most polynomial even on extreme shapes. -/
theorem reciprocal_error_global (k N : ℕ) (p : Path N) :
    |(leadingConstant 2 k * (N : ℝ) ^ (2 * k)) /
      dimensionRatio 2 k (rowVector N p) - 1| ≤
      leadingConstant 2 k * (N : ℝ) ^ (2 * k) + 1 := by
  have hD : 0 ≤ leadingConstant 2 k * (N : ℝ) ^ (2 * k) :=
    mul_nonneg (leadingConstant_pos 2 k (by decide)).le (pow_nonneg (Nat.cast_nonneg _) _)
  have hR := dimensionRatio_ge_one k N p
  have hR0 : 0 < dimensionRatio 2 k (rowVector N p) := lt_of_lt_of_le zero_lt_one hR
  have hdiv : (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) /
      dimensionRatio 2 k (rowVector N p) ≤ leadingConstant 2 k * (N : ℝ) ^ (2 * k) :=
    div_le_self hD hR
  calc
    _ ≤ |(leadingConstant 2 k * (N : ℝ) ^ (2 * k)) /
        dimensionRatio 2 k (rowVector N p)| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg (div_nonneg hD hR0.le), abs_one]; linarith

/-- The exponentially small remainder after the polynomial reciprocal bound. -/
def reciprocalTailEnvelope (k N : ℕ) : ℝ :=
  (leadingConstant 2 k * (N : ℝ) ^ (2 * k) + 1) *
    ((N : ℝ) + 1) * (9 / 10 : ℝ) ^ N

theorem mean_absolute_reciprocal_error (k N : ℕ) (hN : 1 ≤ N) :
    (∑ p : Path N, weight N p *
      |(leadingConstant 2 k * (N : ℝ) ^ (2 * k)) /
        dimensionRatio 2 k (rowVector N p) - 1|) ≤
      (2 : ℝ) ^ (2 * k) * dimensionMomentConstant k / N + reciprocalTailEnvelope k N := by
  let D := leadingConstant 2 k * (N : ℝ) ^ (2 * k)
  have hD : 0 ≤ D :=
    mul_nonneg (leadingConstant_pos 2 k (by decide)).le (pow_nonneg (Nat.cast_nonneg _) _)
  have hpoint (p : Path N) :
      weight N p * |D / dimensionRatio 2 k (rowVector N p) - 1| ≤
        (2 : ℝ) ^ (2 * k) * (weight N p *
          |dimensionRatio 2 k (rowVector N p) / D - 1|) +
            (D + 1) * (if N < 2 * spin N p then weight N p else 0) := by
    by_cases hp : legal N p
    · by_cases ht : N < 2 * spin N p
      · rw [if_pos ht]
        have hb := mul_le_mul_of_nonneg_left (reciprocal_error_global k N p) (weight_nonneg N p)
        have hn : 0 ≤ (2 : ℝ) ^ (2 * k) * (weight N p *
            |dimensionRatio 2 k (rowVector N p) / D - 1|) :=
          mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (weight_nonneg N p) (abs_nonneg _))
        change weight N p * |D / dimensionRatio 2 k (rowVector N p) - 1| ≤
          weight N p * (D + 1) at hb
        nlinarith
      · rw [if_neg ht, mul_zero, add_zero]
        have hb := mul_le_mul_of_nonneg_left
          (reciprocal_error_of_small_gap k N hN p hp (Nat.le_of_not_gt ht)) (weight_nonneg N p)
        convert hb using 1
        ring
    · rw [weight_eq_zero_of_not_legal N p hp]
      simp
  calc
    _ ≤ ∑ p : Path N, ((2 : ℝ) ^ (2 * k) * (weight N p *
        |dimensionRatio 2 k (rowVector N p) / D - 1|) +
          (D + 1) * (if N < 2 * spin N p then weight N p else 0)) :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = (2 : ℝ) ^ (2 * k) * (∑ p : Path N, weight N p *
        |dimensionRatio 2 k (rowVector N p) / D - 1|) +
          (D + 1) * largeGapProbability N := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ ≤ (2 : ℝ) ^ (2 * k) * (dimensionMomentConstant k / N) +
        (D + 1) * (((N : ℝ) + 1) * (9 / 10 : ℝ) ^ N) :=
      add_le_add (mul_le_mul_of_nonneg_left (mean_absolute_dimensionRatio_error k N hN)
        (pow_nonneg (by norm_num) _))
        (mul_le_mul_of_nonneg_left (largeGapProbability_le N) (by linarith))
    _ = _ := by dsimp [reciprocalTailEnvelope, D]; ring

/-- The actual reciprocal Weyl-product moment of the concrete law. -/
def meanInverseDimensionRatio (k N : ℕ) : ℝ :=
  ∑ p : Path N, weight N p / dimensionRatio 2 k (rowVector N p)

theorem meanInverseDimensionRatio_relative_error (k N : ℕ) (hN : 1 ≤ N) :
    |(leadingConstant 2 k * (N : ℝ) ^ (2 * k)) * meanInverseDimensionRatio k N - 1| ≤
      (2 : ℝ) ^ (2 * k) * dimensionMomentConstant k / N + reciprocalTailEnvelope k N := by
  let D := leadingConstant 2 k * (N : ℝ) ^ (2 * k)
  have heq : D * meanInverseDimensionRatio k N - 1 =
      ∑ p : Path N, weight N p * (D / dimensionRatio 2 k (rowVector N p) - 1) := by
    calc
      _ = (∑ p : Path N, D * (weight N p / dimensionRatio 2 k (rowVector N p))) -
          ∑ p : Path N, weight N p := by rw [← Finset.mul_sum, weight_sum]; rfl
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  change |D * meanInverseDimensionRatio k N - 1| ≤ _
  rw [heq]
  calc
    _ ≤ ∑ p : Path N, |weight N p * (D / dimensionRatio 2 k (rowVector N p) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : Path N, weight N p * |D / dimensionRatio 2 k (rowVector N p) - 1| := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_of_nonneg (weight_nonneg N p)]
    _ ≤ _ := mean_absolute_reciprocal_error k N hN

/-- The exponential remainder is smaller than `1/N`, after multiplying by
any fixed polynomial supplied by the ambient dimension. -/
theorem scaled_reciprocalTail_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * reciprocalTailEnvelope k N) atTop (𝓝 0) := by
  have h (j : ℕ) : Tendsto (fun N : ℕ => (N : ℝ) ^ j * (9 / 10 : ℝ) ^ N) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one j (by norm_num) (by norm_num)
  have hl := (((h (2 * k + 2)).const_mul (leadingConstant 2 k)).add
    ((h (2 * k + 1)).const_mul (leadingConstant 2 k))).add ((h 2).add (h 1))
  convert hl using 1
  · funext N
    dsimp [reciprocalTailEnvelope]
    simp only [pow_add, pow_one, pow_two]
    ring
  · simp

/-- An explicit eventual `1/N` bound for the normalized reciprocal moment. -/
theorem meanInverseDimensionRatio_eventual_rate (k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      |(leadingConstant 2 k * (N : ℝ) ^ (2 * k)) * meanInverseDimensionRatio k N - 1| ≤
        ((2 : ℝ) ^ (2 * k) * dimensionMomentConstant k + 1) / N := by
  have ht := (scaled_reciprocalTail_tendsto_zero k).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop 1, ht] with N hN htN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have htail : reciprocalTailEnvelope k N ≤ 1 / (N : ℝ) := by
    apply (le_div_iff₀ hN0).mpr
    nlinarith
  calc
    _ ≤ (2 : ℝ) ^ (2 * k) * dimensionMomentConstant k / N + reciprocalTailEnvelope k N :=
      meanInverseDimensionRatio_relative_error k N hN
    _ ≤ (2 : ℝ) ^ (2 * k) * dimensionMomentConstant k / N + 1 / N :=
      add_le_add le_rfl htail
    _ = _ := by ring

theorem meanInverseDimensionRatio_relative_isBigO (k : ℕ) :
    Asymptotics.IsBigO atTop
      (fun N : ℕ => (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) *
        meanInverseDimensionRatio k N - 1)
      (fun N : ℕ => 1 / (N : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ (2 * k) * dimensionMomentConstant k + 1)
  filter_upwards [meanInverseDimensionRatio_eventual_rate k] with N hN
  have hn : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn, mul_one_div] using hN

theorem meanInverseDimensionRatio_eq_shape_sum (k N : ℕ) :
    meanInverseDimensionRatio k N = ∑ s : Fin (N + 1), shapeProbability N s /
      dimensionRatio 2 k (shapeRowVector N s) := by
  simp only [meanInverseDimensionRatio, div_eq_mul_inv]
  rw [shape_expectation N (fun s => (dimensionRatio 2 k (shapeRowVector N s))⁻¹)]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hl : legal N p
  · rw [rowVector_eq_shapeRowVector N p hl]
  · rw [weight_eq_zero_of_not_legal N p hl]
    simp

/-- The reciprocal moment rate directly under the normalized concrete shape law. -/
theorem shape_inverse_dimensionRatio_relative_isBigO (k : ℕ) :
    Asymptotics.IsBigO atTop
      (fun N : ℕ => (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) *
        (∑ s : Fin (N + 1), shapeProbability N s / dimensionRatio 2 k (shapeRowVector N s)) - 1)
      (fun N : ℕ => 1 / (N : ℝ)) := by
  simpa only [meanInverseDimensionRatio_eq_shape_sum] using meanInverseDimensionRatio_relative_isBigO k

end Cloning.YoungTwoRow
