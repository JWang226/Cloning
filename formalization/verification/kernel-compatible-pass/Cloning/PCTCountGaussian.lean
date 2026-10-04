import Cloning.PCTCountMixture
import Cloning.TensorLANEmbeddingWhiteningGaussian
import Cloning.PCTJointGaussianConvolution

/-! The count mixture has the literal covariance inflation `1+2v`, including its density constant. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal
open Filter MeasureTheory
namespace Cloning.PCTCount
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTJointGaussianLaw Cloning.PCTJointGaussianWhitening
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.MultimodeCoherentGaussianMixture
open Cloning.TensorLAN Cloning.PCTJointGaussianReal Cloning.GaussianAffinity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d s : ℕ}

private theorem flat_pos (i : Fin (d+1)) : 0<flatSpectrum (d+1) i := by
  unfold flatSpectrum
  positivity

theorem whitening_countGaussianMixture
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (hv : 0<v)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0=sqrtSpectrum (flatSpectrum (d+1))) (y : Fin d → ℝ) :
    whiteningDensity (rootWhitening (flatSpectrum (d+1)) flat_pos b hb)
      (countGaussianMixture u hu v) y=
      productDensity (fun _ : Fin d ↦ 1/(2*(1+2*v))) y := by
  let p := flatSpectrum (d+1)
  have hc : Continuous (fun h : Fin d → ℝ ↦ productDensity (fun _ : Fin d ↦ (1/2:ℝ)) (y-h)) := by
    unfold productDensity density
    fun_prop
  have he : (∫ z, productDensity (fun _ : Fin d ↦ (1/2:ℝ))
      (y-whiten p b (tangentClassical u p z)) ∂gaussianProductMeasure (fun _ : Fin s ↦ v)) =
      ∫ h, productDensity (fun _ : Fin d ↦ (1/2:ℝ)) (y-h)
        ∂realProductMeasure (fun _ : Fin d ↦ 1/(4*v)) := by
    rw [← classicalTangentLaw_map_whiten u p flat_pos hu b hb hv,
      integral_map (continuous_whiten p b).aemeasurable hc.aestronglyMeasurable]
    unfold classicalTangentLaw
    simpa only [Function.comp_def] using (integral_map
      (μ := gaussianProductMeasure (fun _ : Fin s ↦ v))
      (continuous_tangentClassical u p).aemeasurable
      (hc.comp (continuous_whiten p b)).aestronglyMeasurable).symm
  calc
    _ = ∫ z, whiteningDensity (rootWhitening p flat_pos b hb)
        (CountMultinomial.shiftedGaussian d (tangentScore u p hu z)) y
          ∂gaussianProductMeasure (fun _ : Fin s ↦ v) := by
      simp only [whiteningDensity, countGaussianMixture, integral_const_mul, p]
    _ = ∫ z, productDensity (fun _ : Fin d ↦ (1/2:ℝ))
        (y-whiten p b (tangentClassical u p z)) ∂gaussianProductMeasure (fun _ : Fin s ↦ v) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact whiteningDensity_translated_covarianceGaussian p flat_pos (flatSpectrum_sum _ (by omega))
        b hb (tangentScore u p hu z) y
    _ = _ := by
      rw [he, PCTJointGaussianConvolution.integral_realProductMeasure_productDensity
        (fun _ : Fin d ↦ (1/2:ℝ)) (fun _ ↦ 1/(4*v)) (fun _ ↦ by norm_num) (fun _ ↦ by positivity)]
      congr 1
      funext i
      field_simp
      ring

theorem whitening_countMixtureDensity_l1_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (v : ℝ) (hv : 0<v)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0=sqrtSpectrum (flatSpectrum (d+1)))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k ↦ ∫ y, |whiteningDensity (rootWhitening (flatSpectrum (d+1)) flat_pos b hb)
      (countMixtureDensity u v (n k)) y-productDensity (fun _ : Fin d ↦ 1/(2*(1+2*v))) y|)
      atTop (𝓝 0) := by
  have hh := countMixtureDensity_l1_tendsto u hu v hv n hn
  convert hh using 1
  funext k
  rw [← whiteningDensity_l1 (rootWhitening (flatSpectrum (d+1)) flat_pos b hb)]
  simp_rw [whitening_countGaussianMixture u hu v hv b hb]

end Cloning.PCTCount
