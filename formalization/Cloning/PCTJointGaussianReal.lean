import Cloning.PCTJointGaussianLaw
import Cloning.GaussianWitness
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Real product Gaussian laws in the precision convention used by the hybrid
fields, and their exact Fourier characterization. -/
noncomputable section
open MeasureTheory
open scoped Topology BigOperators
namespace Cloning.PCTJointGaussianReal
open Cloning.GaussianAffinity Cloning.PCTJointGaussianLaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k : ℕ}

lemma continuous_productDensity (a : Fin k → ℝ) : Continuous (productDensity a) := by
  unfold productDensity density
  fun_prop

def realProductMeasure (a : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (productDensity a x))

lemma realProductMeasure_probability {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) :
    IsProbabilityMeasure (realProductMeasure a) := by
  constructor
  rw [realProductMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_productDensity a ha)
    (Filter.Eventually.of_forall (productDensity_nonneg a)), integral_productDensity a ha]
  exact ENNReal.ofReal_one

lemma integral_realProductMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin k → ℝ) (f : (Fin k → ℝ) → E) :
    (∫ x, f x ∂realProductMeasure a) = ∫ x, productDensity a x • f x := by
  rw [realProductMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_productDensity a).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (productDensity_nonneg a _)]

lemma density_characteristic {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, (density a x : ℂ) * Complex.exp (Complex.I * (t * x : ℝ))) =
      Complex.exp (-((t ^ 2 / (4 * a) : ℝ) : ℂ)) := by
  have hn : ((Real.sqrt a / Real.sqrt Real.pi : ℝ) : ℂ) *
      ((Real.pi : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ) = 1 := by
    rw [← integral_gaussian_complex (by simpa using ha), ← integral_const_mul]
    have he (x : ℝ) : ((Real.sqrt a / Real.sqrt Real.pi : ℝ) : ℂ) *
        Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2) = (density a x : ℂ) := by
      simp only [density, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
        Complex.ofReal_pow]
    simp_rw [he]
    rw [integral_complex_ofReal, integral_density ha, Complex.ofReal_one]
  have he (x : ℝ) : (density a x : ℂ) * Complex.exp (Complex.I * (t * x : ℝ)) =
      ((Real.sqrt a / Real.sqrt Real.pi : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ) ^ 2)) := by
    simp only [density, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul, fourierIntegral_gaussian (by simpa using ha), ← mul_assoc, hn, one_mul]
  congr 1
  push_cast
  ring

lemma realProductMeasure_characteristic {a : Fin k → ℝ} (ha : ∀ i, 0 < a i)
    (t : Fin k → ℝ) :
    (∫ x, Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ)) ∂realProductMeasure a) =
      Complex.exp (-((∑ i, (t i) ^ 2 / (4 * a i) : ℝ) : ℂ)) := by
  rw [integral_realProductMeasure]
  simp only [Complex.real_smul, productDensity, Complex.ofReal_prod, Complex.ofReal_sum,
    Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) =>
    (density (a i) x : ℂ) * Complex.exp (Complex.I * ((t i * x : ℝ) : ℂ)))]
  simp_rw [density_characteristic (ha _)]
  rw [← Complex.exp_sum]
  congr 1
  simp [Complex.ofReal_sum]

lemma realProductMeasure_charFunDual {a : Fin k → ℝ} (ha : ∀ i, 0 < a i)
    (L : StrongDual ℝ (Fin k → ℝ)) :
    charFunDual (realProductMeasure a) L =
      Complex.exp (-((∑ i, (L (Pi.single i 1)) ^ 2 / (4 * a i) : ℝ) : ℂ)) := by
  rw [charFunDual_apply]
  convert realProductMeasure_characteristic ha (fun i => L (Pi.single i 1)) using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [classical_dual_eq, mul_comm _ Complex.I]

lemma realProductMeasure_characteristic_const {v : ℝ} (hv : 0 < v) (t : Fin k → ℝ) :
    (∫ x, Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ))
      ∂realProductMeasure (fun _ : Fin k => 1 / (4 * v))) =
      Complex.exp (-((v * ∑ i, (t i) ^ 2 : ℝ) : ℂ)) := by
  rw [realProductMeasure_characteristic (fun _ => by positivity)]
  congr 3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- Fourier identification of a probability law in the variance `2v`
convention. This is useful after whitening a singular multinomial law. -/
theorem eq_realProductMeasure_of_characteristic {μ : Measure (Fin k → ℝ)}
    [IsFiniteMeasure μ] {v : ℝ} (hv : 0 < v)
    (h : ∀ t : Fin k → ℝ,
      (∫ x, Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ)) ∂μ) =
        Complex.exp (-((v * ∑ i, (t i) ^ 2 : ℝ) : ℂ))) :
    μ = realProductMeasure (fun _ : Fin k => 1 / (4 * v)) := by
  letI := realProductMeasure_probability (fun _ : Fin k => by positivity :
    ∀ _ : Fin k, 0 < 1 / (4 * v))
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  have he (x : Fin k → ℝ) : Complex.exp ((L x : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((∑ i, L (Pi.single i 1) * x i : ℝ) : ℂ)) := by
    rw [classical_dual_eq, mul_comm _ Complex.I]
  simp_rw [he, h, realProductMeasure_characteristic_const hv]

end Cloning.PCTJointGaussianReal
