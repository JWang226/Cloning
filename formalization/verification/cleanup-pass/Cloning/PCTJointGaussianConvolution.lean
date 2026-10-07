import Cloning.PCTJointGaussianReal
import Mathlib.MeasureTheory.Group.Integral

/-! Exact scalar Gaussian convolution in the precision convention of the
hybrid field. The formula holds pointwise, before passing to L¹. -/
noncomputable section
open MeasureTheory
open scoped Topology BigOperators
namespace Cloning.PCTJointGaussianConvolution
open Cloning.GaussianAffinity Cloning.PCTJointGaussianReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k : ℕ}

lemma density_convolution_integrand {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y x : ℝ) :
    density b x * density a (y - x) =
      density (a * b / (a + b)) y * density (a + b) (x - a * y / (a + b)) := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hc : 0 < a * b / (a + b) := div_pos (mul_pos ha hb) (add_pos ha hb)
  have hs : Real.sqrt (a * b / (a + b)) * Real.sqrt (a + b) =
      Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul hc.le, div_mul_cancel₀ _ hab, Real.sqrt_mul ha.le]
  have hp : (Real.sqrt b / Real.sqrt Real.pi) * (Real.sqrt a / Real.sqrt Real.pi) =
      (Real.sqrt (a * b / (a + b)) / Real.sqrt Real.pi) *
        (Real.sqrt (a + b) / Real.sqrt Real.pi) := by
    rw [div_mul_div_comm, div_mul_div_comm, hs, mul_comm (Real.sqrt b)]
  have hq : -b * x ^ 2 + -a * (y - x) ^ 2 =
      -(a * b / (a + b)) * y ^ 2 + -(a + b) * (x - a * y / (a + b)) ^ 2 := by
    field_simp
    <;> ring
  unfold density
  calc
    _ = ((Real.sqrt b / Real.sqrt Real.pi) * (Real.sqrt a / Real.sqrt Real.pi)) *
        Real.exp (-b * x ^ 2 + -a * (y - x) ^ 2) := by rw [Real.exp_add]; ring
    _ = ((Real.sqrt (a * b / (a + b)) / Real.sqrt Real.pi) *
        (Real.sqrt (a + b) / Real.sqrt Real.pi)) *
          Real.exp (-(a * b / (a + b)) * y ^ 2 + -(a + b) * (x - a * y / (a + b)) ^ 2) := by
      rw [hp, hq]
    _ = _ := by rw [Real.exp_add]; ring

lemma integral_density_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    (∫ x, density b x * density a (y - x)) = density (a * b / (a + b)) y := by
  simp_rw [density_convolution_integrand ha hb y]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_density (add_pos ha hb), mul_one]

lemma integrable_density_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    Integrable (fun x => density b x * density a (y - x)) := by
  simp_rw [density_convolution_integrand ha hb y]
  exact ((measurePreserving_sub_right volume (a * y / (a + b))).integrable_comp_of_integrable
    (integrable_density (add_pos ha hb))).const_mul _

lemma integral_productDensity_convolution (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (y : Fin k → ℝ) :
    (∫ x, productDensity b x * productDensity a (y - x)) =
      productDensity (fun i => a i * b i / (a i + b i)) y := by
  simp only [productDensity, ← Finset.prod_mul_distrib, Pi.sub_apply]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i x => density (b i) x * density (a i) (y i - x))]
  exact Finset.prod_congr rfl (fun i _ => integral_density_convolution (ha i) (hb i) (y i))

lemma integral_realProductMeasure_productDensity (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (y : Fin k → ℝ) :
    (∫ x, productDensity a (y - x) ∂realProductMeasure b) =
      productDensity (fun i => a i * b i / (a i + b i)) y := by
  rw [integral_realProductMeasure]
  exact integral_productDensity_convolution a b ha hb y

end Cloning.PCTJointGaussianConvolution
