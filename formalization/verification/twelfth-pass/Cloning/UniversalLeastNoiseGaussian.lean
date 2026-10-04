import Cloning.UniversalLeastNoiseQuantumKernel
import Cloning.UniversalLeastNoiseRecursion
import Cloning.WeylGaussianTwistedConvolution

/-! Sharp anisotropic Gaussian testing of a normalized continuous quantum-positive
multiplier. The proof uses finite positivity, Bochner Cauchy--Schwarz, exact
twisted Gaussian convolution, and a bounded squaring recurrence. No idler state,
CCR representation theorem, or quantum Bochner reconstruction is a premise.

Write `h = (r²-1)/2`, `I(t) = ∫ exp(-∑ᵢ tᵢ|zᵢ|²) f(z) dz`, and
`T(t)ᵢ = (tᵢ²+h²)/(2tᵢ)`. Kernel positivity and exact Gaussian integration give
`|I(t)|² ≤ (∏ᵢ π/(2tᵢ)) |I(T(t))|`. The normalization
`J(t) = (∏ᵢ (tᵢ+h)/π) |I(t)|` therefore satisfies `J(t)² ≤ J(T(t))`.
On the invariant domain `tᵢ ≥ h > 0`, the elementary bound `|f| ≤ 1` gives
`J ≤ 2^d`. The bounded squaring recurrence forces `J ≤ 1`, which is precisely
the sharp Gaussian test. This is sufficient for the thermal fidelity witness;
no assertion of full number-distribution stochastic domination is made. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter
namespace Cloning.MultimodeCoherent
open Cloning.UniversalLeastNoise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ}

lemma integrable_gaussian_multiplier {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    {f : (Fin d → ℂ) → ℂ} (hf : Continuous f) (hb : ∀ a, ‖f a‖ ≤ 1) :
    Integrable (fun a => (gaussianWeight t a : ℂ) * f a) := by
  apply (integrable_gaussianWeight ht).mono'
    (((Complex.continuous_ofReal.comp (continuous_gaussianWeight t)).mul hf).aestronglyMeasurable)
  exact Eventually.of_forall fun a => by
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussianWeight_nonneg _ _)]
    exact mul_le_of_le_one_right (gaussianWeight_nonneg _ _) (hb a)

lemma norm_gaussian_multiplier_le_L1 {t : Fin d → ℝ} (ht : ∀ i, 0 < t i)
    {f : (Fin d → ℂ) → ℂ} (hf : Continuous f) (hb : ∀ a, ‖f a‖ ≤ 1) :
    ‖∫ a, (gaussianWeight t a : ℂ) * f a‖ ≤ ∏ i, Real.pi / t i := by
  calc
    _ ≤ ∫ a, ‖(gaussianWeight t a : ℂ) * f a‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ a, gaussianWeight t a := by
      apply integral_mono (integrable_gaussian_multiplier ht hf hb).norm
        (integrable_gaussianWeight ht)
      intro a
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussianWeight_nonneg _ _)]
      exact mul_le_of_le_one_right (gaussianWeight_nonneg _ _) (hb a)
    _ = _ := integral_gaussianWeight ht

/-- The scalar quantum-positive test has become an exact Gaussian squaring
inequality. -/
lemma IsQuantumPositive.gaussian_squaring {f : (Fin d → ℂ) → ℂ} {r : ℝ}
    (hp : IsQuantumPositive f r) (hzero : f 0 = 1) (hc : Continuous f)
    {t : Fin d → ℝ} (ht : ∀ i, 0 < t i) :
    ‖∫ a, (gaussianWeight t a : ℂ) * f a‖ ^ 2 ≤
      (∏ i, Real.pi / (2 * t i)) *
        ‖∫ a, (gaussianWeight (fun i => gaussianUpdate ((r ^ 2 - 1) / 2) (t i)) a : ℂ) * f a‖ := by
  letI : Fact (Cloning.PositiveKernel.IsNormalizedPositive (quantumPositiveKernel f r)) :=
    ⟨hp.normalizedPositiveKernel hzero⟩
  have h := Cloning.PositiveKernel.integral_cauchySchwarz (quantumPositiveKernel f r)
    (continuous_quantumPositiveKernel hc r) (integrable_gaussianWeight ht) (0 : Fin d → ℂ)
  have hi := integral_integral_gaussian_quantumKernel ht hc (hp.norm_le_one hzero) r
  have he : (fun i => t i / 2 + (r ^ 2 - 1) ^ 2 / (8 * t i)) =
      (fun i => gaussianUpdate ((r ^ 2 - 1) / 2) (t i)) := by
    funext i
    unfold gaussianUpdate
    field_simp
    ring
  rw [he] at hi
  rw [hi] at h
  simp only [quantumPositiveKernel, neg_zero, smul_zero, displacementPhase_zero_left,
    div_self one_ne_zero, one_mul, sub_zero] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
  exact Finset.prod_nonneg fun i _ => (div_pos Real.pi_pos (mul_pos (by norm_num) (ht i))).le

/-- Sharp Gaussian bound for every regular quantum-positive multiplier in
any finite mode count, including correlated, non-Gaussian multipliers. -/
theorem IsQuantumPositive.norm_gaussian_integral_le {f : (Fin d → ℂ) → ℂ} {r : ℝ}
    (hp : IsQuantumPositive f r) (hzero : f 0 = 1) (hc : Continuous f)
    (hr : 1 < r ^ 2) {t : Fin d → ℝ} (ht : ∀ i, (r ^ 2 - 1) / 2 ≤ t i) :
    ‖∫ a, (gaussianWeight t a : ℂ) * f a‖ ≤
      ∏ i, Real.pi / (t i + (r ^ 2 - 1) / 2) := by
  let h : Fin d → ℝ := fun _ => (r ^ 2 - 1) / 2
  have hh : ∀ i, 0 < h i := fun _ => by dsimp [h]; linarith
  let J : GaussianWidths h → ℝ := fun u => ‖∫ a, (gaussianWeight u.1 a : ℂ) * f a‖
  have hL1 : ∀ u, J u ≤ gaussianL1Bound Real.pi u.1 := by
    intro u
    exact norm_gaussian_multiplier_le_L1
      (fun i => (hh i).trans_le (u.2 i)) hc (hp.norm_le_one hzero)
  have hconv : ∀ u, J u ^ 2 ≤ gaussianConvolutionFactor Real.pi u.1 *
      J (updateWidths hh u) := by
    intro u
    exact hp.gaussian_squaring hzero hc (fun i => (hh i).trans_le (u.2 i))
  have hsharp := gaussianSharpBound_of_convolution Real.pi_pos hh J hL1 hconv ⟨t, ht⟩
  simpa only [J, h, abs_of_nonneg (norm_nonneg _), gaussianSharpBound] using hsharp

/-- Every actual covariant CPTP channel satisfies the sharp oscillator
Gaussian test. All multiplier regularity and positivity are derived from the
channel itself. -/
theorem quantumChannel_weyl_gaussian_bound
    (Φ : Cloning.InfiniteTraceClass.QuantumChannel (Fock d) (Fock d)) (r : ℝ)
    (hcov : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ.toLinearMap T))
    (hr : 1 < r ^ 2) {t : Fin d → ℝ} (ht : ∀ i, (r ^ 2 - 1) / 2 ≤ t i) :
    ‖∫ a, (gaussianWeight t a : ℂ) * weylMultiplier Φ.heisenberg r a‖ ≤
      ∏ i, Real.pi / (t i + (r ^ 2 - 1) / 2) := by
  obtain ⟨_, hzero, hc, hp, _⟩ := quantumChannel_regular_quantumPositive_multiplier Φ r hcov
  exact hp.norm_gaussian_integral_le hzero hc hr ht

end Cloning.MultimodeCoherent
