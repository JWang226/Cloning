import Cloning.PCTJointGaussianConvolution
import Cloning.HybridClassicalConvolution

/-! The actual operator-valued L¹ average of classically translated Gaussian
preparations is the preparation with the convolved scalar Gaussian density. -/
noncomputable section
open MeasureTheory Filter
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTHybridMixture
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.GaussianAffinity
open Cloning.PCTJointGaussianReal Cloning.PCTJointGaussianConvolution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma integrable_classical_translation (μ : Measure (Fin k → ℝ)) [IsFiniteMeasure μ]
    (A : Lp (TraceClass H) 1 (volume : Measure (Fin k → ℝ))) :
    Integrable (fun h => classicalTranslation h A) μ := by
  apply (integrable_const ‖A‖).mono' (continuous_classicalTranslation A).aestronglyMeasurable
  exact Eventually.of_forall fun h => (norm_classicalTranslation h A).le

lemma gaussian_classicalAverage_prepareL1 (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (X : TraceClass H) :
    classicalAverage (productDensity b)
      (prepareL1 (productDensity a) (integrable_productDensity a ha) X) =
      prepareL1 (productDensity (fun i => a i * b i / (a i + b i)))
        (integrable_productDensity _ (fun i =>
          div_pos (mul_pos (ha i) (hb i)) (add_pos (ha i) (hb i)))) X := by
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq _ _ (by simp) (by simp)
    (fun s _ _ => (L1.integrable_coeFn _).integrableOn)
    (fun s _ _ => (L1.integrable_coeFn _).integrableOn)
  intro s _ _
  rw [setIntegral_classicalAverage_prepareL1 (productDensity b) (productDensity a)
    (integrable_productDensity b hb) (integrable_productDensity a ha)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (prepareL1_ae
    (productDensity (fun i => a i * b i / (a i + b i)))
    (integrable_productDensity _ (fun i =>
      div_pos (mul_pos (ha i) (hb i)) (add_pos (ha i) (hb i)))) X)] with y hy
  rw [hy, integral_smul_const, integral_complex_ofReal,
    integral_productDensity_convolution a b ha hb]

/-- Averaging the actual L¹ translation action against a Gaussian probability
law adds the classical covariances. This is an equality of L¹ classes and
therefore does not depend on evaluation of arbitrary representatives. -/
theorem gaussian_classical_translation_average (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (X : TraceClass H) :
    (∫ h, classicalTranslation h
      (prepareL1 (productDensity a) (integrable_productDensity a ha) X)
      ∂realProductMeasure b) =
      prepareL1 (productDensity (fun i => a i * b i / (a i + b i)))
        (integrable_productDensity _ (fun i =>
          div_pos (mul_pos (ha i) (hb i)) (add_pos (ha i) (hb i)))) X := by
  rw [integral_realProductMeasure]
  simp only [← Complex.coe_smul]
  exact gaussian_classicalAverage_prepareL1 a b ha hb X

end Cloning.PCTHybridMixture
