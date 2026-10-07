import Cloning.PCTCountGaussian
import Cloning.YoungPhysicalRoundingAnalysis

/-! Actual smoothed PCT count affinity tends to the Gaussian classical cost with inflation `1+2v`. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal
open Filter MeasureTheory
namespace Cloning.PCTCount
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTJointGaussianWhitening Cloning.YoungGeneral Cloning.YoungHyperplane
open Cloning.TensorLAN Cloning.GaussianAffinity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
variable {d s : ℕ}

private theorem flat_pos (i : Fin (d+1)) : 0<flatSpectrum (d+1) i := by
  unfold flatSpectrum
  positivity

def flatCountDensity (d L : ℕ) : rootSpace d → ℝ :=
  CountMultinomial.density d L (flatSpectrum (d+1)) (fun _ ↦ (flat_pos _).le)
    (flatSpectrum_sum _ (by omega))

theorem whiteningDensity_affinity (W : rootSpace d ≃L[ℝ] (Fin d → ℝ))
    (f g : rootSpace d → ℝ) :
    (∫ y, Real.sqrt (whiteningDensity W f y)*Real.sqrt (whiteningDensity W g y))=
      ∫ x, Real.sqrt (f x)*Real.sqrt (g x) := by
  have hJ := (NNReal.coe_nonneg (whiteningJacobian W))
  have he y : Real.sqrt (whiteningDensity W f y)*Real.sqrt (whiteningDensity W g y)=
      whiteningDensity W (fun x ↦ Real.sqrt (f x)*Real.sqrt (g x)) y := by
    simp only [whiteningDensity, Real.sqrt_mul hJ]
    calc
      _ = (Real.sqrt (whiteningJacobian W : ℝ))^2 *
          (Real.sqrt (f (W.symm y))*Real.sqrt (g (W.symm y))) := by ring
      _ = _ := by rw [Real.sq_sqrt hJ]
  simp_rw [he]
  exact whiteningDensity_integral W _

theorem flatCountDensity_l1_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k ↦ ∫ x, |flatCountDensity d (n k) x-CountMultinomial.shiftedGaussian d 0 x|)
      atTop (𝓝 0) := by
  apply CountMultinomial.density_l1_tendsto d n hn
  · exact fun i ↦ tendsto_const_nhds
  · intro i
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))

theorem countAffinity_tendsto_of_pos
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (hv : 0<v) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn0 : ∀ k, 0<n k) :
    Tendsto (fun k ↦ ∫ x, Real.sqrt (countMixtureDensity u v (n k) x)*
      Real.sqrt (flatCountDensity d (n k) x)) atTop (𝓝 (Cloning.classicalValue (1+2*v) (d+1))) := by
  obtain ⟨b,hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (d+1))=d+1)
    (flatSpectrum (d+1)) (fun _ ↦ (flat_pos _).le) (flatSpectrum_sum _ (by omega))
  let W := rootWhitening (flatSpectrum (d+1)) flat_pos b hb
  let f k := whiteningDensity W (countMixtureDensity u v (n k))
  let g k := whiteningDensity W (flatCountDensity d (n k))
  let f₀ := productDensity (fun _ : Fin d ↦ 1/(2*(1+2*v)))
  let g₀ := productDensity (fun _ : Fin d ↦ (1/2:ℝ))
  have hflim : Tendsto (fun k ↦ ∫ y, |f k y-f₀ y|) atTop (𝓝 0) :=
    whitening_countMixtureDensity_l1_tendsto u hu v hv b hb n hn
  have hglim : Tendsto (fun k ↦ ∫ y, |g k y-g₀ y|) atTop (𝓝 0) := by
    have he y : whiteningDensity W (CountMultinomial.shiftedGaussian d 0) y=g₀ y := by
      have ht := whiteningDensity_translated_covarianceGaussian (flatSpectrum (d+1)) flat_pos
        (flatSpectrum_sum _ (by omega)) b hb (0 : rootSpace d) y
      rw [map_zero, sub_zero] at ht
      exact ht
    have hh := flatCountDensity_l1_tendsto d n hn
    have heq k : (∫ y, |g k y-g₀ y|)=
        ∫ x, |flatCountDensity d (n k) x-CountMultinomial.shiftedGaussian d 0 x| := by
      rw [← whiteningDensity_l1 W]
      simp_rw [he]
      rfl
    simpa only [heq] using hh
  have hh := density_affinity_tendsto volume f g f₀ g₀
    (fun k ↦ whiteningDensity_integrable W _ (integrable_countMixtureDensity u v hv (n k) (hn0 k)))
    (fun k ↦ whiteningDensity_integrable W _ (CountMultinomial.integrable_density d (n k) (hn0 k) _ _ _))
    (GaussianAffinity.integrable_productDensity _ (fun _ ↦ by positivity))
    (GaussianAffinity.integrable_productDensity _ (fun _ ↦ by norm_num))
    (fun k y ↦ mul_nonneg (NNReal.coe_nonneg _) (countMixtureDensity_nonneg u v (n k) _))
    (fun k y ↦ mul_nonneg (NNReal.coe_nonneg _) (CountMultinomial.density_nonneg d (n k) _ _ _ _))
    (productDensity_nonneg _) (productDensity_nonneg _)
    (integral_productDensity _ (fun _ ↦ by positivity))
    (fun k ↦ by rw [whiteningDensity_integral]; exact CountMultinomial.integral_density d (n k) (hn0 k) _ _ _)
    hflim hglim
  have ha : (∫ y, Real.sqrt (f₀ y)*Real.sqrt (g₀ y))=Cloning.classicalValue (1+2*v) (d+1) := by
    have he : (fun _ : Fin d ↦ 1/(2*(1+2*v)))=(fun _ : Fin d ↦ (1/2:ℝ)/(1+2*v)) := by
      funext i
      rw [div_div]
    dsimp only [f₀,g₀]
    rw [he]
    simp_rw [mul_comm (Real.sqrt (productDensity (fun _ : Fin d ↦ (1/2:ℝ)/(1+2*v)) _))]
    simpa using integral_product_dilation_eq_classicalValue (d := d+1) (by omega)
      (fun _ ↦ (1/2:ℝ)) (fun _ ↦ by norm_num) (by positivity : 0<1+2*v)
  rw [ha] at hh
  convert hh using 1
  funext k
  exact (whiteningDensity_affinity W _ _).symm

theorem countAffinity_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (hv : 0<v) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k ↦ ∫ x, Real.sqrt (countMixtureDensity u v (n k) x)*
      Real.sqrt (flatCountDensity d (n k) x)) atTop (𝓝 (Cloning.classicalValue (1+2*v) (d+1))) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hn.eventually (eventually_gt_atTop 0))
  have hk : Tendsto (fun j : ℕ ↦ j+K) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ Nat.le_add_right j K) tendsto_id
  apply (tendsto_add_atTop_iff_nat K).mp
  exact countAffinity_tendsto_of_pos u hu v hv (fun j ↦ n (j+K)) (hn.comp hk)
    (fun j ↦ hK (j+K) (by omega))

end Cloning.PCTCount
