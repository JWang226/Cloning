import Cloning.PhysicalCloningConverseChart
import Cloning.HybridClassicalConvolution

/-! Literal preparation of the local Gaussian model as a translated classical
density times the actual displaced product thermal trace-class state. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace Cloning.PhysicalCloningConverse
open Cloning.PCTPhysicalFidelity Cloning.PCTJointGaussianWhitening
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
set_option backward.isDefEq.respectTransparency false
variable {k s : ℕ}

def standardDensity (k : ℕ) : (Fin k → ℝ) → ℝ :=
  GaussianAffinity.productDensity (fun _ => 1/2)

theorem integrable_standardDensity (k : ℕ) : Integrable (standardDensity k) :=
  GaussianAffinity.integrable_productDensity _ (fun _ => by norm_num)

theorem standardDensity_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ standardDensity k x :=
  GaussianAffinity.productDensity_nonneg _ x

theorem integral_standardDensity (k : ℕ) : (∫ x, standardDensity k x) = 1 :=
  GaussianAffinity.integral_productDensity _ (fun _ => by norm_num)

def translatedStandardDensity (h : Fin k → ℝ) : (Fin k → ℝ) → ℝ :=
  fun x => standardDensity k (x-h)

theorem integrable_translatedStandardDensity (h : Fin k → ℝ) :
    Integrable (translatedStandardDensity h) :=
  (measurePreserving_sub_right volume h).integrable_comp_of_integrable (integrable_standardDensity k)

def displacedProductThermal (p : SimpleSpectrum (k+1)) (e : Fin s ≃ PairIndex (k+1))
    (z : Fin s → ℂ) : TraceClass (Fock s) :=
  displacementTraceMap z (vectorMixture (numberBasis s) (productGeometric (fun i => p.ratio (e i))))

theorem classicalTranslation_prepare_standard (h : Fin k → ℝ) (X : TraceClass (Fock s)) :
    classicalTranslation h (prepareL1 (standardDensity k) (integrable_standardDensity k) X) =
      prepareL1 (translatedStandardDensity h) (integrable_translatedStandardDensity h) X := by
  apply Lp.ext
  exact (classicalTranslation_prepareL1_ae _ (integrable_standardDensity k) h X).trans
    (prepareL1_ae _ (integrable_translatedStandardDensity h) X).symm

/-- Equality in the actual operator-valued L¹ space, with all normalization,
translation and thermal-vector-mixture adapters discharged. -/
theorem model_eq_prepare_translated (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (θ : Parameters k) :
    (model p b e θ).1 =
      prepareL1 (translatedStandardDensity (whiten p.eigenvalue b θ.1))
        (integrable_translatedStandardDensity _) (displacedProductThermal p e (fun i => θ.2 (e i))) := by
  rw [model_val]
  change hybridTranslation (parameterTranslation p b e θ)
    (gaussianThermalField _ _ _ _ _).toL1 = _
  rw [gaussianThermalField_toL1]
  change hybridTranslation (whiten p.eigenvalue b θ.1,fun i => θ.2 (e i))
    (prepareL1 (standardDensity k) (integrable_standardDensity k) _) = _
  rw [Cloning.PCTHybridMixture.hybridTranslation_prepare, classicalTranslation_prepare_standard]
  rfl

end Cloning.PhysicalCloningConverse
