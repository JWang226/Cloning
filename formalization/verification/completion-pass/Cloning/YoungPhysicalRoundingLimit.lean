import Cloning.YoungPhysicalRoundingAnalysis

/-! The literal randomized dilation of physical Young labels converges in L¹. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
open Cloning.YoungRounding
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def headGaussian (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1) : (Fin d → ℝ) → ℝ :=
  coordinateDensity d (covarianceGaussian d p hp)

theorem headGaussian_nonneg (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1)
    (x : Fin d → ℝ) : 0 ≤ headGaussian d p hp x :=
  mul_nonneg (Real.sqrt_nonneg _) (covarianceGaussian_nonneg d p hp _)

theorem integral_headGaussian (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 < p i) : (∫ x, headGaussian d p hp x) = 1 := by
  rw [headGaussian, integral_coordinateDensity, integral_covarianceGaussian d p hp hp0]

theorem integrable_headGaussian (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1)
    (hp0 : ∀ i, 0 < p i) : Integrable (headGaussian d p hp) := by
  by_contra hi
  have hh := integral_headGaussian d p hp hp0
  rw [integral_undef hi] at hh
  norm_num at hh

theorem continuous_headGaussian (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∑ i, p i = 1) :
    Continuous (headGaussian d p hp) := by
  have hc := (covarianceEigenbasis d p hp).repr.continuous.comp (coordinatesContinuous d).continuous
  have hi (i : Fin d) : Continuous (fun x : Fin d → ℝ ↦
      (covarianceEigenbasis d p hp).repr (coordinates d x) i) :=
    (PiLp.continuous_apply 2 _ i).comp hc
  unfold headGaussian coordinateDensity covarianceGaussian GaussianAffinity.productDensity
  apply Continuous.const_mul
  apply continuous_finset_prod
  intro i _
  unfold GaussianAffinity.density
  exact (Real.continuous_exp.comp ((hi i).pow 2 |>.const_mul (- (1 / (2 * covarianceEigenvalues d p hp i))))).const_mul _

theorem integrable_headDensity (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Integrable (headDensity d N p hp hs) :=
  integrable_affineDensity _ (by positivity) _
    (integrable_interpolate (ENNReal.summable_toReal (tensorYoungHeadPMF d N p hp hs).tsum_coe_ne_top))

theorem headDensity_nonneg (d N : ℕ)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (x : Fin d → ℝ) :
    0 ≤ headDensity d N p hp hs x := by
  unfold headDensity affineDensity YoungRounding.interpolate
  positivity

theorem integral_headDensity (d N : ℕ) (hN : 0 < N)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∫ x, headDensity d N p hp hs x) = 1 := by
  rw [← coordinateDensity_tensorYoungDensity, integral_coordinateDensity,
    integral_tensorYoungDensity d N hN]

/-- Exact recentering of the raw dilation: its fluctuation scale is sqrt(m/n). -/
theorem preRoundedDensity_eq_dilated_headDensity (d n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    preRoundedDensity (Real.sqrt (m : ℝ))⁻¹ (headAnchor d m p) ((m : ℝ)/n)
      (tensorYoungHeadPMF d n p hp hs) =
    affineDensity (Real.sqrt (m : ℝ)/Real.sqrt (n : ℝ)) 0 (headDensity d n p hp hs) := by
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsm : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hscale : (Real.sqrt (m : ℝ))⁻¹*((m : ℝ)/n) =
      (Real.sqrt (m : ℝ)/Real.sqrt (n : ℝ))*(Real.sqrt (n : ℝ))⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg m)]
  have hanchor : headAnchor d m p =
      (Real.sqrt (m : ℝ)/Real.sqrt (n : ℝ)) • headAnchor d n p := by
    ext i
    simp only [headAnchor, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [preRoundedDensity, headDensity,
    affineDensity_comp _ _ (inv_ne_zero hsm) (div_ne_zero hmR hnR),
    affineDensity_comp _ _ (div_ne_zero hsm hsn) (inv_ne_zero hsn)]
  simp only [smul_zero, add_zero, zero_add, hscale, hanchor]

/-- Arbitrary divergent input/output sizes and moving strict spectra yield the actual
rounded output density, with covariance dilated by the limiting sample ratio. -/
theorem rounded_tensorYoungDensity_l1_tendsto (d : ℕ) (n m : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (hn0 : ∀ k, 0 < n k) (hm0 : ∀ k, 0 < m k)
    (γ : ℝ) (hγ : 0 < γ) (hratio : Tendsto (fun k ↦ (m k : ℝ)/n k) atTop (𝓝 γ))
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ k, ∑ i, p k i = 1)
    (hp0 : ∀ k i, 0 < p k i) (p₀ : Fin (d + 1) → ℝ) (hs₀ : ∑ i, p₀ i = 1)
    (hp₀ : ∀ i, 0 < p₀ i) (hord : StrictAnti p₀)
    (hlim : ∀ i, Tendsto (fun k ↦ p k i) atTop (𝓝 (p₀ i))) :
    Tendsto (fun k ↦ ∫ x, |roundedDensity (Real.sqrt (m k : ℝ))⁻¹ (headAnchor d (m k) (p k))
      ((m k : ℝ)/n k) (tensorYoungHeadPMF d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k)) x -
      affineDensity (Real.sqrt γ) 0 (headGaussian d p₀ hs₀) x|) atTop (𝓝 0) := by
  let s := fun k ↦ Real.sqrt (m k : ℝ)/Real.sqrt (n k : ℝ)
  have hs : ∀ k, 0 < s k := fun k ↦ by dsimp [s]; positivity [hn0 k, hm0 k]
  have hsconv : Tendsto s atTop (𝓝 (Real.sqrt γ)) := by
    simpa only [s, Real.sqrt_div (Nat.cast_nonneg _)] using hratio.sqrt
  have hbase := headDensity_l1_tendsto d n hn hn0 p hp hp0 p₀ hs₀ hp₀ hord hlim
  have hpre := affineDensity_l1_tendsto s hs (Real.sqrt γ) (by positivity) hsconv
    (fun k ↦ headDensity d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k))
    (fun k ↦ integrable_headDensity d (n k) (hn0 k) (p k) _ (hp k))
    (headGaussian d p₀ hs₀) (integrable_headGaussian d p₀ hs₀ hp₀)
    (headGaussian_nonneg d p₀ hs₀) (continuous_headGaussian d p₀ hs₀) hbase
  apply roundedDensity_l1_tendsto_of_pre
    (fun k ↦ (Real.sqrt (m k : ℝ))⁻¹) (fun k ↦ (m k : ℝ)/n k)
    (fun k ↦ headAnchor d (m k) (p k))
    (fun k ↦ tensorYoungHeadPMF d (n k) (p k) (fun i ↦ (hp0 k i).le) (hp k))
    (fun k ↦ by positivity [hm0 k]) (fun k ↦ by positivity [hm0 k, hn0 k])
    (Cloning.YoungMultinomial.inv_sqrt_nat_tendsto_zero.comp hm)
    (affineDensity (Real.sqrt γ) 0 (headGaussian d p₀ hs₀))
    (integrable_affineDensity _ (by positivity) _ (integrable_headGaussian d p₀ hs₀ hp₀))
    (fun x ↦ mul_nonneg (by positivity) (headGaussian_nonneg d p₀ hs₀ _))
    (by
      unfold affineDensity
      exact ((continuous_headGaussian d p₀ hs₀).comp
        ((continuous_id.sub continuous_const).const_smul _)).const_mul _)
  simpa only [preRoundedDensity_eq_dilated_headDensity d _ _ (hn0 _) (hm0 _), s] using hpre

end Cloning.YoungHyperplane
