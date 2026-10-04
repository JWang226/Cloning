import Cloning.YoungPhysicalRoundingCoordinates
import Cloning.HybridIntegralBounds
import Cloning.ClassicalFidelity

/-! Analytic transport and affinity bounds for the physical rounding limit. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungRounding
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]

/-- Scalar affine transports compose with their exact density Jacobians. -/
theorem affineDensity_comp (h k : ℝ) (hh : h ≠ 0) (hk : k ≠ 0)
    (a b : ι → ℝ) (f : (ι → ℝ) → ℝ) :
    affineDensity h a (affineDensity k b f) = affineDensity (h*k) (a + h • b) f := by
  funext x
  simp only [affineDensity, mul_pow, mul_inv_rev]
  have harg : k⁻¹ • (h⁻¹ • (x-a)-b) = (h*k)⁻¹ • (x-(a+h • b)) := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
    field_simp
    <;> ring
  rw [harg]
  ring

/-- A fixed continuous density is L¹-continuous under positive scalar dilation. -/
theorem affineDensity_l1_tendsto_scale (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (s₀ : ℝ) (hs₀ : 0 < s₀) (hlim : Tendsto s atTop (𝓝 s₀))
    (f : (ι → ℝ) → ℝ) (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f) :
    Tendsto (fun n ↦ ∫ x, |affineDensity (s n) 0 f x - affineDensity s₀ 0 f x|) atTop (𝓝 0) := by
  apply YoungHyperplane.density_scheffe volume
    (fun n ↦ affineDensity (s n) 0 f) (affineDensity s₀ 0 f)
    (fun n ↦ integrable_affineDensity (s n) (hs n) 0 hf)
    (integrable_affineDensity s₀ hs₀ 0 hf)
    (fun n x ↦ mul_nonneg (inv_nonneg.mpr (pow_nonneg (hs n).le _)) (hf0 _))
    (fun x ↦ mul_nonneg (inv_nonneg.mpr (pow_nonneg hs₀.le _)) (hf0 _))
  · intro n
    rw [integral_affineDensity (s n) (hs n), integral_affineDensity s₀ hs₀]
  · apply ae_of_all
    intro x
    have harg : Tendsto (fun n ↦ (s n)⁻¹ • (x-(0 : ι → ℝ))) atTop
        (𝓝 (s₀⁻¹ • (x-(0 : ι → ℝ)))) := (hlim.inv₀ hs₀.ne').smul tendsto_const_nhds
    exact ((hlim.pow (Fintype.card ι)).inv₀ (pow_ne_zero _ hs₀.ne')).mul
      (hfc.continuousAt.tendsto.comp harg)

/-- Scalar dilation transports an actual L¹ density limit, even with moving scales. -/
theorem affineDensity_l1_tendsto (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (s₀ : ℝ) (hs₀ : 0 < s₀) (hlim : Tendsto s atTop (𝓝 s₀))
    (f : ℕ → (ι → ℝ) → ℝ) (hf : ∀ n, Integrable (f n))
    (g : (ι → ℝ) → ℝ) (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x) (hgc : Continuous g)
    (hfg : Tendsto (fun n ↦ ∫ x, |f n x-g x|) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, |affineDensity (s n) 0 (f n) x-affineDensity s₀ 0 g x|)
      atTop (𝓝 0) := by
  have hsc := affineDensity_l1_tendsto_scale s hs s₀ hs₀ hlim g hg hg0 hgc
  have hadd := hfg.add hsc
  simp only [add_zero] at hadd
  apply squeeze_zero (fun n ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) ?_ hadd
  intro n
  rw [← affineDensity_l1_isometry (s n) (hs n) 0 (f n) g]
  have hfi := integrable_affineDensity (s n) (hs n) 0 (hf n)
  have hgi := integrable_affineDensity (s n) (hs n) 0 hg
  have hzi := integrable_affineDensity s₀ hs₀ 0 hg
  erw [← integral_add (hfi.sub hgi).abs (hgi.sub hzi).abs]
  apply integral_mono (hfi.sub hzi).abs ((hfi.sub hgi).abs.add (hgi.sub hzi).abs)
  intro x
  exact abs_sub_le _ _ _

/-- The proved cell-average error upgrades any L¹ pre-rounding limit to the actual output. -/
theorem roundedDensity_l1_tendsto_of_pre
    (h γ : ℕ → ℝ) (a : ℕ → ι → ℝ) (p : ℕ → PMF (ι → ℤ))
    (hh : ∀ n, 0 < h n) (hγ : ∀ n, 0 < γ n) (hlim : Tendsto h atTop (𝓝 0))
    (g : (ι → ℝ) → ℝ) (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x) (hgc : Continuous g)
    (hpre : Tendsto (fun n ↦ ∫ x, |preRoundedDensity (h n) (a n) (γ n) (p n) x-g x|)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, |roundedDensity (h n) (a n) (γ n) (p n) x-g x|)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsource := hpre.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))
  filter_upwards [hsource, scaledCellAverage_l1_tendsto_uniform_translation
    hg hg0 hgc h hh hlim (ε/2) (by positivity)] with n hn hnav
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ ↦ abs_nonneg _))]
  have hb := roundedDensity_l1_comparison (h n) (hh n) (a n) (γ n) (hγ n) (p n) hg
  have ha := hnav (a n)
  linarith

end Cloning.YoungRounding

namespace Cloning.YoungHyperplane
variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- Continuous-density counterpart of the discrete Hellinger perturbation bound. -/
theorem density_affinity_l1_bound (f g r : X → ℝ)
    (hf : Integrable f ν) (hg : Integrable g ν) (hr : Integrable r ν)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hr0 : ∀ x, 0 ≤ r x)
    (hrmass : (∫ x, r x ∂ν) = 1) :
    |(∫ x, Real.sqrt (f x)*Real.sqrt (r x) ∂ν) -
      ∫ x, Real.sqrt (g x)*Real.sqrt (r x) ∂ν| ≤
      Real.sqrt (∫ x, |f x-g x| ∂ν) := by
  have hfi := Hybrid.integrable_sqrt_mul_sqrt hf hr hf0 hr0
  have hgi := Hybrid.integrable_sqrt_mul_sqrt hg hr hg0 hr0
  have hbi := Hybrid.integrable_sqrt_mul_sqrt (hf.sub hg).abs hr
    (fun _ ↦ abs_nonneg _) hr0
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ∫ x, |Real.sqrt (f x)*Real.sqrt (r x)-Real.sqrt (g x)*Real.sqrt (r x)| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, Real.sqrt |f x-g x| * Real.sqrt (r x) ∂ν := by
      apply integral_mono (hfi.sub hgi).abs hbi
      intro x
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (ClassicalFidelity.sqrt_difference_bound _ _ (hf0 x) (hg0 x)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (∫ x, |f x-g x| ∂ν) * Real.sqrt (∫ x, r x ∂ν) :=
      Hybrid.integral_sqrt_mul_sqrt_le (hf.sub hg).abs hr (fun _ ↦ abs_nonneg _) hr0
    _ = _ := by rw [hrmass, Real.sqrt_one, mul_one]

/-- Joint L¹ convergence of probability densities implies convergence of affinity. -/
theorem density_affinity_tendsto (f g : ℕ → X → ℝ) (f₀ g₀ : X → ℝ)
    (hf : ∀ n, Integrable (f n) ν) (hg : ∀ n, Integrable (g n) ν)
    (hf₀ : Integrable f₀ ν) (hg₀ : Integrable g₀ ν)
    (hf0 : ∀ n x, 0 ≤ f n x) (hg0 : ∀ n x, 0 ≤ g n x)
    (hf₀0 : ∀ x, 0 ≤ f₀ x) (hg₀0 : ∀ x, 0 ≤ g₀ x)
    (hfmass : (∫ x, f₀ x ∂ν) = 1) (hgmass : ∀ n, (∫ x, g n x ∂ν) = 1)
    (hflim : Tendsto (fun n ↦ ∫ x, |f n x-f₀ x| ∂ν) atTop (𝓝 0))
    (hglim : Tendsto (fun n ↦ ∫ x, |g n x-g₀ x| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, Real.sqrt (f n x)*Real.sqrt (g n x) ∂ν) atTop
      (𝓝 (∫ x, Real.sqrt (f₀ x)*Real.sqrt (g₀ x) ∂ν)) := by
  have hb n : |(∫ x, Real.sqrt (f n x)*Real.sqrt (g n x) ∂ν) -
      ∫ x, Real.sqrt (f₀ x)*Real.sqrt (g₀ x) ∂ν| ≤
      Real.sqrt (∫ x, |f n x-f₀ x| ∂ν) + Real.sqrt (∫ x, |g n x-g₀ x| ∂ν) := by
    apply (abs_sub_le _ (∫ x, Real.sqrt (f₀ x)*Real.sqrt (g n x) ∂ν) _).trans
    apply add_le_add (density_affinity_l1_bound ν _ _ _ (hf n) hf₀ (hg n)
      (hf0 n) hf₀0 (hg0 n) (hgmass n))
    simpa only [mul_comm] using density_affinity_l1_bound ν _ _ _ (hg n) hg₀ hf₀
      (hg0 n) hg₀0 hf₀0 hfmass
  have hh := (hflim.sqrt).add hglim.sqrt
  simp only [Real.sqrt_zero, add_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun n ↦ abs_nonneg _) hb hh

end Cloning.YoungHyperplane
