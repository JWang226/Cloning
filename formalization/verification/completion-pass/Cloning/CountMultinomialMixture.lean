import Cloning.CountMultinomialMeasurability
import Mathlib.MeasureTheory.Integral.Prod

/-! Dominated L¹ convergence for actual mixtures of probability densities. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace Cloning.CountMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
variable (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]

theorem integrable_joint_density (f : Z → X → ℝ)
    (hm : Measurable (Function.uncurry f)) (hf : ∀ z, Integrable (f z) ν)
    (h0 : ∀ z x, 0≤f z x) (h1 : ∀ z, (∫ x, f z x ∂ν)=1) :
    Integrable (Function.uncurry f) (μ.prod ν) := by
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hf, ?_⟩
  simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (h0 _ _), h1]
  exact integrable_const _

theorem integral_mixture_density (f : Z → X → ℝ)
    (hm : Measurable (Function.uncurry f)) (hf : ∀ z, Integrable (f z) ν)
    (h0 : ∀ z x, 0≤f z x) (h1 : ∀ z, (∫ x, f z x ∂ν)=1) :
    (∫ x, (∫ z, f z x ∂μ) ∂ν)=1 := by
  rw [← integral_integral_swap (integrable_joint_density μ ν f hm hf h0 h1)]
  simp only [h1, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]

theorem mixture_l1_le (f g : Z → X → ℝ)
    (hf : Integrable (Function.uncurry f) (μ.prod ν))
    (hg : Integrable (Function.uncurry g) (μ.prod ν)) :
    (∫ x, |(∫ z, f z x ∂μ)-(∫ z, g z x ∂μ)| ∂ν) ≤
      ∫ z, (∫ x, |f z x-g z x| ∂ν) ∂μ := by
  have he := hf.sub hg
  calc
    _ ≤ ∫ x, (∫ z, |f z x-g z x| ∂μ) ∂ν := by
      apply integral_mono_ae (hf.integral_prod_right.sub hg.integral_prod_right).abs
        he.abs.integral_prod_right
      filter_upwards [hf.prod_left_ae, hg.prod_left_ae] with x hfx hgx
      change |(∫ z, f z x ∂μ)-(∫ z, g z x ∂μ)| ≤ ∫ z, |f z x-g z x| ∂μ
      change Integrable (fun z ↦ f z x) μ at hfx
      change Integrable (fun z ↦ g z x) μ at hgx
      rw [← integral_sub hfx hgx]
      exact abs_integral_le_integral_abs
    _ = _ := (integral_integral_swap he.abs).symm

theorem mixture_density_l1_tendsto (f : ℕ → Z → X → ℝ) (g : Z → X → ℝ)
    (hfm : ∀ n, Measurable (Function.uncurry (f n)))
    (hgm : Measurable (Function.uncurry g))
    (hfi : ∀ n z, Integrable (f n z) ν) (hgi : ∀ z, Integrable (g z) ν)
    (hf0 : ∀ n z x, 0≤f n z x) (hg0 : ∀ z x, 0≤g z x)
    (hf1 : ∀ n z, (∫ x, f n z x ∂ν)=1) (hg1 : ∀ z, (∫ x, g z x ∂ν)=1)
    (hlim : ∀ z, Tendsto (fun n ↦ ∫ x, |f n z x-g z x| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, |(∫ z, f n z x ∂μ)-(∫ z, g z x ∂μ)| ∂ν)
      atTop (𝓝 0) := by
  have hjf n := integrable_joint_density μ ν (f n) (hfm n) (hfi n) (hf0 n) (hf1 n)
  have hjg := integrable_joint_density μ ν g hgm hgi hg0 hg1
  have hb n z : (∫ x, |f n z x-g z x| ∂ν) ≤ 2 := by
    calc
      _ ≤ ∫ x, f n z x+g z x ∂ν := by
        apply integral_mono ((hfi n z).sub (hgi z)).abs ((hfi n z).add (hgi z))
        intro x
        change |f n z x-g z x| ≤ f n z x+g z x
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (hf0 n z x), abs_of_nonneg (hg0 z x)] using abs_sub_le (f n z x) 0 (g z x)
      _ = 2 := by rw [integral_add (hfi n z) (hgi z), hf1, hg1]; norm_num
  have ht : Tendsto (fun n ↦ ∫ z, (∫ x, |f n z x-g z x| ∂ν) ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (fun _ : Z ↦ (2:ℝ))
      (fun n ↦ ((hjf n).sub hjg).abs.integral_prod_left.aestronglyMeasurable)
      (integrable_const _)
      (fun n ↦ Eventually.of_forall (fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ abs_nonneg _))]
        exact hb n z)) (Eventually.of_forall hlim)
    simpa using hh
  exact squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
    (fun n ↦ mixture_l1_le μ ν (f n) g (hjf n) hjg) ht

end Cloning.CountMultinomial
