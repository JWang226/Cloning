import Cloning.PCTCountParameters
import Cloning.CountMultinomialMixture

/-! The actual PCT conditional count limit integrates over the full Gaussian tangent law. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter MeasureTheory
namespace Cloning.PCTCount
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState Cloning.PCTLocalChart
open Cloning.PCTGaussianCovariance Cloning.PCTJointGaussianLaw Cloning.PCTJointGaussianWhitening
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 180000
variable {d s : ℕ}

theorem continuous_particleProbability
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (L : ℕ) (i : Fin (d+1)) : Continuous (fun z ↦ particleProbability u z L i) := by
  have hc (a b : Fin (d+1)) : Continuous (fun z ↦ frameParticle u z L (a,b)) := by
    simp only [frameParticle_apply]
    exact continuous_finset_sum _ (fun j _ ↦ (GeneralCoherent.continuous_oneParticle s L j).mul_const _)
  unfold particleProbability reducedDensityMatrix
  exact Complex.continuous_re.comp (continuous_finset_sum _ (fun j _ ↦ (hc i j).mul (hc i j).star))

theorem continuous_tangentScore
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (p : Fin (d+1) → ℝ) (hu : u 0=coefficientVector (schmidtCoefficients p)) :
    Continuous (tangentScore u p hu) := by
  apply Continuous.subtype_mk
  exact (PiLp.continuous_toLp 2 _).comp (continuous_tangentClassical u p)

theorem continuous_shiftedGaussian (d : ℕ) :
    Continuous (fun hx : rootSpace d × rootSpace d ↦ CountMultinomial.shiftedGaussian d hx.1 hx.2) := by
  unfold CountMultinomial.shiftedGaussian
  simp_rw [covarianceGaussian_eq_exp d (flatSpectrum (d+1)) _
    (fun _ ↦ by unfold flatSpectrum; positivity)]
  fun_prop

def countMixtureDensity
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (v : ℝ) (L : ℕ) (x : rootSpace d) : ℝ :=
  ∫ z, CountMultinomial.density d L (particleProbability u z L)
    (particleProbability_nonneg u z L) (particleProbability_sum u z L) x
    ∂gaussianProductMeasure (fun _ : Fin s ↦ v)

def countGaussianMixture
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (x : rootSpace d) : ℝ :=
  ∫ z, CountMultinomial.shiftedGaussian d (tangentScore u (flatSpectrum (d+1)) hu z) x
    ∂gaussianProductMeasure (fun _ : Fin s ↦ v)

theorem countMixtureDensity_nonneg
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (v : ℝ) (L : ℕ) (x : rootSpace d) : 0≤countMixtureDensity u v L x :=
  integral_nonneg (fun z ↦ CountMultinomial.density_nonneg d L _ _ _ x)

set_option backward.isDefEq.respectTransparency true in
theorem measurable_count_conditional
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (L : ℕ) (hL : 0<L) :
    Measurable (fun zx : (Fin s → ℂ)×rootSpace d ↦ CountMultinomial.density d L
      (particleProbability u zx.1 L) (particleProbability_nonneg u zx.1 L)
      (particleProbability_sum u zx.1 L) zx.2) :=
  CountMultinomial.measurable_density_uncurry d L hL (fun z ↦ particleProbability u z L)
    (fun z ↦ particleProbability_nonneg u z L) (fun z ↦ particleProbability_sum u z L)
    (continuous_particleProbability u L)

theorem integral_countMixtureDensity
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (v : ℝ) (hv : 0<v) (L : ℕ) (hL : 0<L) : (∫ x, countMixtureDensity u v L x)=1 := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s ↦ hv)
  exact CountMultinomial.integral_mixture_density _ volume _
    (measurable_count_conditional u L hL)
    (fun _ ↦ CountMultinomial.integrable_density d L hL _ _ _)
    (fun _ ↦ CountMultinomial.density_nonneg d L _ _ _)
    (fun _ ↦ CountMultinomial.integral_density d L hL _ _ _)

theorem integrable_countMixtureDensity
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (v : ℝ) (hv : 0<v) (L : ℕ) (hL : 0<L) : Integrable (countMixtureDensity u v L) := by
  by_contra hi
  have hh := integral_countMixtureDensity u v hv L hL
  rw [integral_undef hi] at hh
  norm_num at hh

theorem countMixtureDensity_l1_tendsto_of_pos
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (hv : 0<v) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0<n k) :
    Tendsto (fun k ↦ ∫ x, |countMixtureDensity u v (n k) x-countGaussianMixture u hu v x|)
      atTop (𝓝 0) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s ↦ hv)
  unfold countMixtureDensity countGaussianMixture
  apply CountMultinomial.mixture_density_l1_tendsto
  · intro k
    exact measurable_count_conditional u (n k) (hn0 k)
  · exact ((continuous_shiftedGaussian d).comp
      (((continuous_tangentScore u _ hu).comp continuous_fst).prodMk continuous_snd)).measurable
  · intro k z
    exact CountMultinomial.integrable_density d (n k) (hn0 k) _ _ _
  · exact fun z ↦ CountMultinomial.integrable_shiftedGaussian d _
  · exact fun k z ↦ CountMultinomial.density_nonneg d (n k) _ _ _
  · exact fun z ↦ CountMultinomial.shiftedGaussian_nonneg d _
  · exact fun k z ↦ CountMultinomial.integral_density d (n k) (hn0 k) _ _ _
  · exact fun z ↦ CountMultinomial.integral_shiftedGaussian d _
  · exact fun z ↦ conditional_count_density_l1_tendsto u hu z n hn

theorem countMixtureDensity_l1_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (hv : 0<v) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k ↦ ∫ x, |countMixtureDensity u v (n k) x-countGaussianMixture u hu v x|)
      atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hn.eventually (eventually_gt_atTop 0))
  have hk : Tendsto (fun j : ℕ ↦ j+K) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ Nat.le_add_right j K) tendsto_id
  apply (tendsto_add_atTop_iff_nat K).mp
  exact countMixtureDensity_l1_tendsto_of_pos u hu v hv (fun j ↦ n (j+K)) (hn.comp hk)
    (fun j ↦ hK (j+K) (by omega))

end Cloning.PCTCount
