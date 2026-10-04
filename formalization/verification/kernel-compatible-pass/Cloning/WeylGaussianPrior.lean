import Cloning.WeylCovariantization
import Cloning.CoherentGaussianMixture
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi

/-! Explicit expanding Gaussian priors and their proved L¹ translation
continuity on finite-dimensional phase space. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Standard product circular Gaussian, as a literal Lebesgue density. -/
def priorDensity (z : Fin d → ℂ) : ℝ :=
  ∏ i, CoherentGaussianMixture.gaussianDensity 1 (z i)

lemma priorDensity_pos (z : Fin d → ℂ) : 0 < priorDensity z := by
  apply Finset.prod_pos
  intro i _
  exact CoherentGaussianMixture.gaussianDensity_pos (by norm_num) _

lemma continuous_priorDensity : Continuous (priorDensity (d := d)) := by
  unfold priorDensity
  exact continuous_finset_prod _ (fun i _ =>
    (CoherentGaussianMixture.continuous_gaussianDensity 1).comp (continuous_apply i))

lemma priorDensity_integral : (∫ z : Fin d → ℂ, priorDensity z) = 1 := by
  unfold priorDensity
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [CoherentGaussianMixture.gaussianDensity_integral (by norm_num : (0 : ℝ) < 1),
    Finset.prod_const_one]

lemma integrable_priorDensity : Integrable (priorDensity (d := d)) :=
  integrable_of_integral_eq_one priorDensity_integral

/-- The base probability prior; each complex coordinate has variance one. -/
def gaussianPrior (d : ℕ) : Measure (Fin d → ℂ) :=
  volume.withDensity (fun z => ENNReal.ofReal (priorDensity z))

instance gaussianPrior_probability (d : ℕ) : IsProbabilityMeasure (gaussianPrior d) := by
  constructor
  rw [gaussianPrior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_priorDensity
    (Eventually.of_forall (fun z => (priorDensity_pos z).le)), priorDensity_integral]
  exact ENNReal.ofReal_one

/-- Expansion by a factor `n+1`, giving variance `(n+1)^2` in every mode. -/
def expandingGaussianPrior (d n : ℕ) : Measure (Fin d → ℂ) :=
  (gaussianPrior d).map (fun a => ((n : ℝ) + 1) • a)

instance expandingGaussianPrior_probability (d n : ℕ) :
    IsProbabilityMeasure (expandingGaussianPrior d n) := by
  unfold expandingGaussianPrior
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- L¹ translation continuity is proved from Mathlib's continuous
measure-preserving action on L¹, for the actual finite-dimensional Haar measure. -/
theorem integral_abs_translate_sub_tendsto (p : (Fin d → ℂ) → ℝ) (hp : Integrable p) :
    Tendsto (fun a : Fin d → ℂ => ∫ x, |p (a + x) - p x|) (𝓝 0) (𝓝 0) := by
  let f : Lp ℝ 1 (volume : Measure (Fin d → ℂ)) := hp.toL1 p
  let shifts : C((Fin d → ℂ), C((Fin d → ℂ), (Fin d → ℂ))) :=
    (ContinuousMap.mk (fun z : (Fin d → ℂ) × (Fin d → ℂ) => z.1 + z.2) continuous_add).curry
  have hm (a : Fin d → ℂ) : MeasurePreserving (shifts a) volume volume :=
    measurePreserving_add_left volume a
  have hc : Continuous (fun a => Lp.compMeasurePreserving (shifts a) (hm a) f) :=
    continuous_const.compMeasurePreservingLp shifts.continuous hm (by norm_num)
  have he (a : Fin d → ℂ) :
      ‖Lp.compMeasurePreserving (shifts a) (hm a) f - f‖ = ∫ x, |p (a + x) - p x| := by
    have hi := (hm a).integrable_comp_of_integrable hp
    change ‖hi.toL1 (fun x => p (a + x)) - hp.toL1 p‖ = _
    rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hz : Lp.compMeasurePreserving (shifts 0) (hm 0) f = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving f (hm 0)] with x hx
    simpa [shifts] using hx
  have h := ((hc.tendsto 0).sub_const f).norm
  simpa only [hz, sub_self, norm_zero, he] using h

/-- The translation error for the rescaled prior tends to zero for every
fixed physical displacement. -/
theorem prior_translation_error_tendsto (b : Fin d → ℂ) :
    Tendsto (fun n : ℕ => ∫ x, |priorDensity (-(((n : ℝ) + 1)⁻¹ • b) + x) -
      priorDensity x|) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (hi.smul_const b).neg
  have h' : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹ • b)) atTop (𝓝 0) := by
    simpa only [zero_smul, neg_zero] using h
  exact (integral_abs_translate_sub_tendsto priorDensity integrable_priorDensity).comp h'

end Cloning.MultimodeCoherent
