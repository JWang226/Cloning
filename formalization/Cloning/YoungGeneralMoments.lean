import Cloning.YoungGeneralPMF
import Cloning.YoungCompatibilityPMF
import Cloning.YoungDimensionRatio

/-!
# General-rank crossing-dimension moment limits

The expectations are under genuine PMFs identified with the explicit tableau
formula at the flat spectrum.  Their tails are proved in the preceding files,
and the dimension observable is the literal crossing-root Weyl product.
No moment or concentration premise is assumed.  Representation-space
dimension identification and Schur measurement identification remain separate.
-/

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace Cloning.YoungGeneral
open YoungDimensionRatio

def flatSpectrum (r : ℕ) : Fin r → ℝ := fun _ ↦ 1 / r

theorem flatSpectrum_sum (r : ℕ) (hr : 0 < r) : ∑ i, flatSpectrum r i = 1 := by
  simp [flatSpectrum, (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr) : (r : ℝ) ≠ 0)]

def shapeRows {r N : ℕ} (μ : Shape r N) : Fin r → ℝ := fun i ↦ (μ i).val

theorem shapeRows_nonneg {r N : ℕ} (μ : Shape r N) (i : Fin r) : 0 ≤ shapeRows μ i :=
  Nat.cast_nonneg _

theorem shapeRows_le {r N : ℕ} (μ : Shape r N) (i : Fin r) : shapeRows μ i ≤ N := by
  dsimp only [shapeRows]
  exact_mod_cast Nat.le_of_lt_succ (μ i).isLt

def dimensionErrorEnvelope (r k N : ℕ) : ℝ :=
  Real.exp ((r * k : ℕ) * ((r : ℝ) * shrinkingRadius N + (r : ℝ) * ((r : ℝ) + k) / N)) - 1

theorem dimensionErrorEnvelope_nonneg (r k N : ℕ) : 0 ≤ dimensionErrorEnvelope r k N := by
  unfold dimensionErrorEnvelope
  apply sub_nonneg.mpr
  apply Real.one_le_exp_iff.mpr
  have := shrinkingRadius_nonneg N
  positivity

theorem dimensionErrorEnvelope_tendsto_zero (r k : ℕ) :
    Tendsto (dimensionErrorEnvelope r k) atTop (𝓝 0) :=
  error_envelope_tendsto_zero r k (fun N ↦ (N : ℝ)) shrinkingRadius
    tendsto_natCast_atTop_atTop shrinkingRadius_tendsto_zero

def normalizedDimension (r k N : ℕ) (μ : Shape r N) : ℝ :=
  dimensionRatio r k (shapeRows μ) / (leadingConstant r k * (N : ℝ) ^ (r * k))

def dimensionUniformBound (r k : ℕ) : ℝ := ((r : ℝ) * (1 + r + k)) ^ (r * k) + 1

theorem normalizedDimension_global_error (r k N : ℕ) (hr : 0 < r) (hN : 1 ≤ N)
    (μ : Shape r N) : |normalizedDimension r k N μ - 1| ≤ dimensionUniformBound r k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : leadingConstant r k * (N : ℝ) ^ (r * k) ≠ 0 :=
    (mul_pos (leadingConstant_pos r k hr) (pow_pos hn _)).ne'
  unfold normalizedDimension
  rw [dimensionRatio_factorization r k (shapeRows μ) N hr hn, mul_div_cancel_left₀ _ hden]
  have hpos (a : Fin r × Fin k) : 0 ≤ (r : ℝ) * (shapeRows μ a.1 + crossingGap a) / N := by
    have := shapeRows_nonneg μ a.1
    have := (crossingGap_pos a).le
    positivity
  have hb (a : Fin r × Fin k) :
      (r : ℝ) * (shapeRows μ a.1 + crossingGap a) / N ≤ (r : ℝ) * (1 + r + k) := by
    have hrow := shapeRows_le μ a.1
    have hgap := crossingGap_le a
    have hc : 0 ≤ (r : ℝ) + k := by positivity
    have hcN := mul_le_mul_of_nonneg_left hn1 hc
    apply (div_le_iff₀ hn).mpr
    have hinside : shapeRows μ a.1 + crossingGap a ≤ (1 + r + k) * (N : ℝ) := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg r)]
  have hprod := Finset.prod_le_prod (fun a (_ : a ∈ (Finset.univ : Finset (Fin r × Fin k))) ↦ hpos a)
    (fun a _ ↦ hb a)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hprod
  have hprod0 : 0 ≤ ∏ a : Fin r × Fin k, (r : ℝ) * (shapeRows μ a.1 + crossingGap a) / N :=
    Finset.prod_nonneg (fun a _ ↦ hpos a)
  have hab := abs_sub (∏ a : Fin r × Fin k, (r : ℝ) * (shapeRows μ a.1 + crossingGap a) / N) (1 : ℝ)
  rw [abs_of_nonneg hprod0, abs_one] at hab
  unfold dimensionUniformBound
  linarith

theorem normalizedDimension_typical_error (r k N : ℕ) (hr : 0 < r) (hN : 1 ≤ N)
    (μ : Shape r N)
    (ht : ¬∃ i, (N : ℝ) * shrinkingRadius N ≤ |shapeRows μ i - N * flatSpectrum r i|) :
    |normalizedDimension r k N μ - 1| ≤ dimensionErrorEnvelope r k N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply dimensionRatio_relative_error r k (shapeRows μ) N (shrinkingRadius N) hr hn
  intro i
  have hi := lt_of_not_ge (fun h ↦ ht ⟨i, h⟩)
  have heq : shapeRows μ i / N - 1 / (r : ℝ) =
      (shapeRows μ i - N * flatSpectrum r i) / N := by
        unfold flatSpectrum
        field_simp
  rw [heq, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  nlinarith

/-- Finite expectation splitting with the actual coordinate tail. -/
theorem mean_error_le {r N : ℕ} (P : PMF (Shape r N)) (p : Fin r → ℝ)
    (ε δ B : ℝ) (hδ : 0 ≤ δ) (F : Shape r N → ℝ)
    (hglobal : ∀ μ, |F μ - 1| ≤ B)
    (hgood : ∀ μ, (¬∃ i, (N : ℝ) * ε ≤ |((μ i).val : ℝ) - N * p i|) → |F μ - 1| ≤ δ) :
    (∑ μ, (P μ).toReal * |F μ - 1|) ≤ δ + B * tailProbability P p ε := by
  have hpoint (μ : Shape r N) : (P μ).toReal * |F μ - 1| ≤ (P μ).toReal * δ +
      B * (if ∃ i, (N : ℝ) * ε ≤ |((μ i).val : ℝ) - N * p i| then (P μ).toReal else 0) := by
    split_ifs with ht
    · have hb := mul_le_mul_of_nonneg_left (hglobal μ) (show 0 ≤ (P μ).toReal from ENNReal.toReal_nonneg)
      have hz := mul_nonneg (show 0 ≤ (P μ).toReal from ENNReal.toReal_nonneg) hδ
      nlinarith
    · simp only [mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood μ ht) ENNReal.toReal_nonneg
  have hs : ∑ μ, (P μ).toReal = 1 := by
    simpa only [tsum_fintype, YoungCompatibility.probability] using YoungCompatibility.tsum_probability P
  have hsum := Finset.sum_le_sum (fun μ (_ : μ ∈ (Finset.univ : Finset (Shape r N))) ↦ hpoint μ)
  simpa only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hs, one_mul,
    tailProbability] using hsum

/-- General-rank forward dimension moment: convergence in mean absolute
relative error, under the exact flat Young formula. -/
theorem mean_normalizedDimension_error_tendsto_zero (r k : ℕ) (hr : 0 < r)
    (P : ∀ N, PMF (Shape r N))
    (hformula : ∀ N μ, (P N μ).toReal = youngWeight N (flatSpectrum r) (fun i ↦ (μ i).val)) :
    Tendsto (fun N ↦ ∑ μ, (P N μ).toReal * |normalizedDimension r k N μ - 1|) atTop (𝓝 0) := by
  have htail := tailProbability_tendsto_zero P (fun _ ↦ flatSpectrum r)
    (fun _ _ ↦ by dsimp [flatSpectrum]; positivity) (fun _ ↦ flatSpectrum_sum r hr)
    (fun _ ↦ antitone_const) hformula
  have hbound := (dimensionErrorEnvelope_tendsto_zero r k).add (htail.const_mul (dimensionUniformBound r k))
  simp only [mul_zero, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun N ↦
    Finset.sum_nonneg (fun μ _ ↦ mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)))) ?_ hbound
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact mean_error_le (P N) (flatSpectrum r) (shrinkingRadius N)
    (dimensionErrorEnvelope r k N) (dimensionUniformBound r k)
    (dimensionErrorEnvelope_nonneg r k N) (normalizedDimension r k N)
    (normalizedDimension_global_error r k N hr hN) (normalizedDimension_typical_error r k N hr hN)

def inverseNormalizedDimension (r k N : ℕ) (μ : Shape r N) : ℝ :=
  (leadingConstant r k * (N : ℝ) ^ (r * k)) / dimensionRatio r k (shapeRows μ)

theorem dimensionRatio_shape_ge_one (r k N : ℕ) (μ : Shape r N) :
    1 ≤ dimensionRatio r k (shapeRows μ) := by
  apply Finset.one_le_prod
  intro a _
  apply (one_le_div (crossingGap_pos a)).mpr
  exact le_add_of_nonneg_left (shapeRows_nonneg μ a.1)

theorem inverseNormalizedDimension_global_error (r k N : ℕ) (hr : 0 < r)
    (μ : Shape r N) :
    |inverseNormalizedDimension r k N μ - 1| ≤ leadingConstant r k * (N : ℝ) ^ (r * k) + 1 := by
  let D := leadingConstant r k * (N : ℝ) ^ (r * k)
  have hD : 0 ≤ D := mul_nonneg (leadingConstant_pos r k hr).le (pow_nonneg (Nat.cast_nonneg _) _)
  have hR := dimensionRatio_shape_ge_one r k N μ
  have hR0 : 0 < dimensionRatio r k (shapeRows μ) := lt_of_lt_of_le zero_lt_one hR
  have hdiv : D / dimensionRatio r k (shapeRows μ) ≤ D := div_le_self hD hR
  have hab := abs_sub (D / dimensionRatio r k (shapeRows μ)) (1 : ℝ)
  rw [abs_of_nonneg (div_nonneg hD hR0.le), abs_one] at hab
  change |D / dimensionRatio r k (shapeRows μ) - 1| ≤ D + 1
  linarith

private theorem inverse_error_of_error {R D δ : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hδ : δ ≤ 1 / 2) (herr : |R / D - 1| ≤ δ) : |D / R - 1| ≤ 2 * δ := by
  have hl : (1 / 2 : ℝ) ≤ R / D := by have := (abs_le.mp herr).1; linarith
  have hl' : D ≤ 2 * R := by have := (le_div_iff₀ hD).mp hl; linarith
  have hinv : D / R ≤ 2 := (div_le_iff₀ hR).mpr hl'
  have heq : D / R - 1 = -(D / R) * (R / D - 1) := by field_simp; ring
  rw [heq, abs_mul, abs_neg, abs_of_pos (div_pos hD hR)]
  exact (mul_le_mul_of_nonneg_left herr (div_pos hD hR).le).trans
    (mul_le_mul_of_nonneg_right hinv (le_trans (abs_nonneg _) herr))

theorem inverseNormalizedDimension_typical_error (r k N : ℕ) (hr : 0 < r) (hN : 1 ≤ N)
    (hsmall : dimensionErrorEnvelope r k N ≤ 1 / 2) (μ : Shape r N)
    (ht : ¬∃ i, (N : ℝ) * shrinkingRadius N ≤ |shapeRows μ i - N * flatSpectrum r i|) :
    |inverseNormalizedDimension r k N μ - 1| ≤ 2 * dimensionErrorEnvelope r k N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact inverse_error_of_error (dimensionRatio_pos r k (shapeRows μ) (shapeRows_nonneg μ))
    (mul_pos (leadingConstant_pos r k hr) (pow_pos hn _)) hsmall
    (normalizedDimension_typical_error r k N hr hN μ ht)

/-- General-rank reciprocal dimension moment.  Polynomial growth on extreme
shapes is controlled by the proved stretched-exponential Young tail. -/
theorem mean_inverseNormalizedDimension_error_tendsto_zero (r k : ℕ) (hr : 0 < r)
    (P : ∀ N, PMF (Shape r N))
    (hformula : ∀ N μ, (P N μ).toReal = youngWeight N (flatSpectrum r) (fun i ↦ (μ i).val)) :
    Tendsto (fun N ↦ ∑ μ, (P N μ).toReal * |inverseNormalizedDimension r k N μ - 1|)
      atTop (𝓝 0) := by
  let c := leadingConstant r k
  let a := r * k
  have hc : 0 ≤ c := (leadingConstant_pos r k hr).le
  have htail := (polynomial_concentrationEnvelope_tendsto_zero r a).const_mul (c + 1)
  have hbound := ((dimensionErrorEnvelope_tendsto_zero r k).const_mul 2).add htail
  simp only [mul_zero, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun N ↦
    Finset.sum_nonneg (fun μ _ ↦ mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)))) ?_ hbound
  have hsmall : ∀ᶠ N in atTop, dimensionErrorEnvelope r k N ≤ 1 / 2 :=
    (dimensionErrorEnvelope_tendsto_zero r k).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop 1, hsmall] with N hN heN
  have hmean := mean_error_le (P N) (flatSpectrum r) (shrinkingRadius N)
    (2 * dimensionErrorEnvelope r k N) (c * (N : ℝ) ^ a + 1)
    (mul_nonneg (by norm_num) (dimensionErrorEnvelope_nonneg r k N))
    (inverseNormalizedDimension r k N)
    (inverseNormalizedDimension_global_error r k N hr)
    (inverseNormalizedDimension_typical_error r k N hr hN heN)
  have htailN : tailProbability (P N) (flatSpectrum r) (shrinkingRadius N) ≤ concentrationEnvelope r N := by
    rw [tailProbability_eq_atypicalMass _ _ (hformula N)]
    exact atypicalMass_shrinking_le N hN (flatSpectrum r)
      (fun _ ↦ by dsimp [flatSpectrum]; positivity) (flatSpectrum_sum r hr) antitone_const
  have hpw : (N : ℝ) ^ a ≤ ((N : ℝ) + 1) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpw1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ a := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hcoeff : c * (N : ℝ) ^ a + 1 ≤ (c + 1) * ((N : ℝ) + 1) ^ a := by
    nlinarith [mul_le_mul_of_nonneg_left hpw hc]
  have ht0 : 0 ≤ tailProbability (P N) (flatSpectrum r) (shrinkingRadius N) := by
    unfold tailProbability
    exact Finset.sum_nonneg (fun μ _ ↦ by split_ifs <;> positivity)
  have htailbound : (c * (N : ℝ) ^ a + 1) * tailProbability (P N) (flatSpectrum r) (shrinkingRadius N) ≤
      (c + 1) * (((N : ℝ) + 1) ^ a * concentrationEnvelope r N) := by
    have hh := mul_le_mul hcoeff htailN ht0 (by positivity : 0 ≤ (c + 1) * ((N : ℝ) + 1) ^ a)
    convert hh using 1 <;> ring
  exact hmean.trans (by linarith)

theorem mean_tendsto_one_of_mean_absolute_error {r : ℕ} (P : ∀ N, PMF (Shape r N))
    (F : ∀ N, Shape r N → ℝ)
    (h : Tendsto (fun N ↦ ∑ μ, (P N μ).toReal * |F N μ - 1|) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∑ μ, (P N μ).toReal * F N μ) atTop (𝓝 1) := by
  have herr : Tendsto (fun N ↦ (∑ μ, (P N μ).toReal * F N μ) - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N ↦ ?_) h
    have hs : ∑ μ, (P N μ).toReal = 1 := by
      simpa only [tsum_fintype, YoungCompatibility.probability] using
        YoungCompatibility.tsum_probability (P N)
    have heq : (∑ μ, (P N μ).toReal * F N μ) - 1 =
        ∑ μ, (P N μ).toReal * (F N μ - 1) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hs]
    rw [heq, Real.norm_eq_abs]
    simpa only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
      Finset.abs_sum_le_sum_abs (fun μ : Shape r N ↦ (P N μ).toReal * (F N μ - 1)) Finset.univ
  simpa only [sub_add_cancel, zero_add] using herr.add_const 1

/-- Forward and inverse leading-order moments in every rank. -/
theorem dimension_moments_tendsto_one (r k : ℕ) (hr : 0 < r)
    (P : ∀ N, PMF (Shape r N))
    (hformula : ∀ N μ, (P N μ).toReal = youngWeight N (flatSpectrum r) (fun i ↦ (μ i).val)) :
    Tendsto (fun N ↦ ∑ μ, (P N μ).toReal * normalizedDimension r k N μ) atTop (𝓝 1) ∧
    Tendsto (fun N ↦ ∑ μ, (P N μ).toReal * inverseNormalizedDimension r k N μ) atTop (𝓝 1) :=
  ⟨mean_tendsto_one_of_mean_absolute_error P _ (mean_normalizedDimension_error_tendsto_zero r k hr P hformula),
    mean_tendsto_one_of_mean_absolute_error P _ (mean_inverseNormalizedDimension_error_tendsto_zero r k hr P hformula)⟩

end Cloning.YoungGeneral
