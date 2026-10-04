import Cloning.YoungMultinomialLocal

/-!
# Uniform moving-window multinomial local limit

The spectrum may change arbitrarily with sample size. A uniform positive lower
bound and a fixed central-window radius suffice; no convergence of spectra or
lattice centers is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.YoungMultinomial

theorem inv_sqrt_nat_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Uniform local Gaussian approximation along arbitrary moving spectra and
central lattice points. The Gaussian denominator is explicit, and both its
entropy and factorial errors are proved above. -/
theorem multinomialMass_div_gaussianMass_tendsto_one_subsequence {ι : Type*} [Fintype ι]
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (p x : ℕ → ι → ℝ) (μ : ℕ → ι → ℕ) (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R)
    (hp : ∀ᶠ N in atTop, ∀ i, a ≤ p N i)
    (hx : ∀ᶠ N in atTop, ∀ i, |x N i| ≤ R)
    (hsum : ∀ N, ∑ i, p N i = 1) (hzero : ∀ N, ∑ i, x N i = 0)
    (hcount : ∀ N i, (μ N i : ℝ) = (n N : ℝ) * (p N i + x N i / Real.sqrt (n N))) :
    Tendsto (fun N ↦ multinomialMass (n N) (p N) (μ N) / gaussianMass (n N) (p N) (x N))
      atTop (𝓝 1) := by
  have hsmall : ∀ᶠ N : ℕ in atTop, R / Real.sqrt (n N : ℝ) ≤ a / 2 := by
    have hh : Tendsto (fun N : ℕ ↦ R / Real.sqrt (n N : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (inv_sqrt_nat_tendsto_zero.comp hn).const_mul R
    exact (hh.eventually (eventually_lt_nhds (show (0 : ℝ) < a / 2 by positivity))).mono
      (fun _ h ↦ h.le)
  have hq : ∀ᶠ N : ℕ in atTop, ∀ i, a / 2 ≤ p N i + x N i / Real.sqrt (n N) := by
    filter_upwards [hp, hx, hsmall, hn.eventually (eventually_ge_atTop 1)] with N hpN hxN hsmallN hN i
    have hnN : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by omega)
    have hs : 0 < Real.sqrt (n N : ℝ) := Real.sqrt_pos.mpr hnN
    have hδ : |x N i / Real.sqrt (n N)| ≤ a / 2 := by
      rw [abs_div, abs_of_pos hs]
      exact (div_le_div_of_nonneg_right (hxN i) hs.le).trans hsmallN
    linarith [hpN i, neg_abs_le (x N i / Real.sqrt (n N))]
  have hst i : Tendsto (fun N ↦ stirlingResidual (μ N i)) atTop (𝓝 0) := by
    have hb : ∀ᶠ N : ℕ in atTop, a / 2 * (n N : ℝ) ≤ (μ N i : ℝ) := by
      filter_upwards [hq] with N hqN
      rw [hcount]
      nlinarith [mul_le_mul_of_nonneg_left (hqN i) (Nat.cast_nonneg (n N))]
    have ht : Tendsto (fun N ↦ (μ N i : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop hb
        ((tendsto_natCast_atTop_atTop.comp hn).const_mul_atTop (by positivity : (0 : ℝ) < a / 2))
    exact stirlingResidual_tendsto_zero.comp (tendsto_natCast_atTop_iff.mp ht)
  have hstsum : Tendsto (fun N ↦ ∑ i, stirlingResidual (μ N i)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ ↦ hst i)
  have hu i : Tendsto (fun N ↦ x N i / Real.sqrt (n N) / p N i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      (show Tendsto (fun N : ℕ ↦ R / a * (Real.sqrt (n N : ℝ))⁻¹) atTop (𝓝 0) by
        simpa using (inv_sqrt_nat_tendsto_zero.comp hn).const_mul (R / a))
    filter_upwards [hp, hx, hn.eventually (eventually_ge_atTop 1)] with N hpN hxN hN
    have hnN : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by omega)
    have hs : 0 < Real.sqrt (n N : ℝ) := Real.sqrt_pos.mpr hnN
    have hpN0 : 0 < p N i := ha.trans_le (hpN i)
    rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hs, abs_of_pos hpN0]
    calc
      _ ≤ R / Real.sqrt (n N) / a := by gcongr; exact hxN i; exact hpN i
      _ = _ := by ring
  have hlog i : Tendsto (fun N ↦ Real.log ((p N i + x N i / Real.sqrt (n N)) / p N i))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N ↦ 1 + x N i / Real.sqrt (n N) / p N i) atTop (𝓝 1) := by
      simpa using (hu i).const_add 1
    have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
    simp only [Real.log_one] at hh
    apply hh.congr'
    filter_upwards [hp] with N hpN
    have hpN0 : p N i ≠ 0 := (ha.trans_le (hpN i)).ne'
    dsimp only [Function.comp_apply]
    congr 1
    field_simp
  let entropyError := fun N : ℕ ↦ (n N : ℝ) *
      (∑ i, (p N i + x N i / Real.sqrt (n N)) *
        Real.log ((p N i + x N i / Real.sqrt (n N)) / p N i)) -
      ∑ i, (x N i) ^ 2 / (2 * p N i)
  have he : Tendsto entropyError atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      (show Tendsto (fun N : ℕ ↦ 4 * Fintype.card ι * R ^ 3 / a ^ 2 *
        (Real.sqrt (n N : ℝ))⁻¹) atTop (𝓝 0) by
          simpa using (inv_sqrt_nat_tendsto_zero.comp hn).const_mul (4 * Fintype.card ι * R ^ 3 / a ^ 2))
    filter_upwards [hp, hx, hsmall, hn.eventually (eventually_ge_atTop 1)] with N hpN hxN hsN hN
    simpa only [entropyError, Real.norm_eq_abs, div_mul_eq_div_mul_one_div, one_div] using
      central_entropy_bound (p N) (x N) (n N) a R
        (by exact_mod_cast (show 0 < n N by omega)) ha hR hpN hxN hsN (hzero N)
  have hl : Tendsto (fun N ↦ Real.log (multinomialMass (n N) (p N) (μ N)) -
      gaussianLogMass (n N) (p N) (x N)) atTop (𝓝 0) := by
    have hlogsum : Tendsto (fun N ↦ ∑ i, Real.log ((p N i + x N i / Real.sqrt (n N)) / p N i))
        atTop (𝓝 0) := by
      simpa using tendsto_finset_sum Finset.univ (fun i _ ↦ hlog i)
    have hh := ((he.neg.sub (hlogsum.const_mul (1 / 2))).add (stirlingResidual_tendsto_zero.comp hn)).sub hstsum
    simp only [neg_zero, mul_zero, sub_zero, zero_add] at hh
    apply hh.congr'
    filter_upwards [hp, hq, hn.eventually (eventually_ge_atTop 1)] with N hpN hqN hN
    exact (central_log_error_eq (n N) (p N) (x N) (μ N) (fun i ↦ ha.trans_le (hpN i))
      (by omega) (hsum N) (hzero N) (fun i ↦ (by positivity : (0 : ℝ) < a / 2).trans_le (hqN i))
      (hcount N)).symm
  have hh := Real.continuous_exp.continuousAt.tendsto.comp hl
  simp only [Real.exp_zero] at hh
  apply hh.congr'
  filter_upwards [hp] with N hpN
  simp only [Function.comp_apply, Real.exp_sub, gaussianMass,
    Real.exp_log (multinomialMass_pos (n N) (p N) (μ N) (fun i ↦ ha.trans_le (hpN i)))]

/-- The usual sample-size version of the uniform moving-window limit. -/
theorem multinomialMass_div_gaussianMass_tendsto_one {ι : Type*} [Fintype ι]
    (p x : ℕ → ι → ℝ) (μ : ℕ → ι → ℕ) (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R)
    (hp : ∀ᶠ N in atTop, ∀ i, a ≤ p N i)
    (hx : ∀ᶠ N in atTop, ∀ i, |x N i| ≤ R)
    (hsum : ∀ N, ∑ i, p N i = 1) (hzero : ∀ N, ∑ i, x N i = 0)
    (hcount : ∀ N i, (μ N i : ℝ) = N * (p N i + x N i / Real.sqrt N)) :
    Tendsto (fun N ↦ multinomialMass N (p N) (μ N) / gaussianMass N (p N) (x N))
      atTop (𝓝 1) :=
  multinomialMass_div_gaussianMass_tendsto_one_subsequence id tendsto_id p x μ a R ha hR
    hp hx hsum hzero hcount

end Cloning.YoungMultinomial
