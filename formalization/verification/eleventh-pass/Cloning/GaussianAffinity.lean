import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Cloning.Main
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual Gaussian density affinities

The normalized precision-parameter density below has variance `1 / (2*a)`.
The affinity is a Lebesgue integral, evaluated using Mathlib's Gaussian
integral and finite-product Fubini theorem, rather than an assumed formula.
-/

noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace Cloning.GaussianAffinity

/-- Centered normalized Gaussian density with positive precision parameter. -/
def density (a x : ℝ) : ℝ :=
  (Real.sqrt a / Real.sqrt Real.pi) * Real.exp (-a * x ^ 2)

theorem density_nonneg (a x : ℝ) : 0 ≤ density a x := by
  unfold density
  positivity

theorem integrable_density {a : ℝ} (ha : 0 < a) : Integrable (density a) :=
  (integrable_exp_neg_mul_sq ha).const_mul _

theorem integral_density {a : ℝ} (ha : 0 < a) : ∫ x, density a x = 1 := by
  unfold density
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  have hs : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  field_simp

theorem sqrt_density (a x : ℝ) :
    Real.sqrt (density a x) = Real.sqrt (Real.sqrt a / Real.sqrt Real.pi) *
      Real.exp (-(a / 2) * x ^ 2) := by
  unfold density
  rw [Real.sqrt_mul (by positivity), ← Real.exp_half]
  congr 2
  ring

theorem integral_sqrt_density_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, Real.sqrt (density a x) * Real.sqrt (density b x)) =
      Real.sqrt (2 * Real.sqrt a * Real.sqrt b / (a + b)) := by
  have hexp (x : ℝ) :
      Real.sqrt (density a x) * Real.sqrt (density b x) =
      (Real.sqrt (Real.sqrt a / Real.sqrt Real.pi) *
        Real.sqrt (Real.sqrt b / Real.sqrt Real.pi)) *
          Real.exp (-((a + b) / 2) * x ^ 2) := by
    rw [sqrt_density, sqrt_density]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hexp]
  rw [integral_const_mul, integral_gaussian,
    ← Real.sqrt_mul (by positivity : 0 ≤ Real.sqrt a / Real.sqrt Real.pi),
    ← Real.sqrt_mul (by positivity :
      0 ≤ (Real.sqrt a / Real.sqrt Real.pi) * (Real.sqrt b / Real.sqrt Real.pi))]
  congr 1
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

/-- Root affinity between one Gaussian and its variance dilation. -/
theorem integral_dilated_density {a g : ℝ} (ha : 0 < a) (hg : 0 < g) :
    (∫ x, Real.sqrt (density a x) * Real.sqrt (density (a / g) x)) =
      Real.sqrt (Cloning.Thermal.classicalBase g) := by
  rw [integral_sqrt_density_mul ha (div_pos ha hg), Real.sqrt_div ha.le]
  congr 1
  unfold Cloning.Thermal.classicalBase
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hsg : Real.sqrt g ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg)
  have ha0 := ne_of_gt ha
  have hg0 := ne_of_gt hg
  have hag : a + a / g ≠ 0 := ne_of_gt (add_pos ha (div_pos ha hg))
  have hg1 : 1 + g ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt ha.le, Real.sq_sqrt hg.le]
  ring

variable {ι : Type*} [Fintype ι]

/-- An actual product Gaussian density, with coordinate-dependent variances. -/
def productDensity (a : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, density (a i) (x i)

theorem productDensity_nonneg (a : ι → ℝ) (x : ι → ℝ) :
    0 ≤ productDensity a x :=
  Finset.prod_nonneg (fun _ _ => density_nonneg _ _)

theorem integral_productDensity (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∫ x, productDensity a x = 1 := by
  unfold productDensity
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [integral_density (ha _), Finset.prod_const_one]

/-- Exact affinity of finite product Gaussian distributions. -/
theorem integral_product_affinity (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∫ x, Real.sqrt (productDensity a x) * Real.sqrt (productDensity b x)) =
      ∏ i, Real.sqrt (2 * Real.sqrt (a i) * Real.sqrt (b i) / (a i + b i)) := by
  simp_rw [productDensity, Real.sqrt_prod _ (fun i _ => density_nonneg _ _),
    ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i t => Real.sqrt (density (a i) t) * Real.sqrt (density (b i) t))]
  exact Finset.prod_congr rfl (fun i _ => integral_sqrt_density_mul (ha i) (hb i))

/-- The classical Gaussian dilation factor in any finite number of coordinates. -/
theorem integral_product_dilation (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {g : ℝ} (hg : 0 < g) :
    (∫ x, Real.sqrt (productDensity a x) *
      Real.sqrt (productDensity (fun i => a i / g) x)) =
      Cloning.Thermal.classicalBase g ^ ((Fintype.card ι : ℝ) / 2) := by
  simp_rw [productDensity, Real.sqrt_prod _ (fun i _ => density_nonneg _ _),
    ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i t => Real.sqrt (density (a i) t) * Real.sqrt (density (a i / g) t))]
  simp_rw [integral_dilated_density (ha _) hg]
  rw [Finset.prod_const, Finset.card_univ, Real.sqrt_eq_rpow,
    ← Real.rpow_mul_natCast (Cloning.Thermal.classicalBase_pos hg).le]
  congr 1
  ring

/-- The manuscript's `F_cl(g,d)` is the actual Gaussian affinity in `d-1`
coordinates; the base precision in each coordinate cancels. -/
theorem integral_product_dilation_eq_classicalValue {d : ℕ} (hd : 1 ≤ d)
    (a : Fin (d - 1) → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 0 < g) :
    (∫ x, Real.sqrt (productDensity a x) *
      Real.sqrt (productDensity (fun i => a i / g) x)) = Cloning.classicalValue g d := by
  rw [integral_product_dilation a ha hg]
  simp only [Fintype.card_fin, Cloning.classicalValue, Nat.cast_sub hd, Nat.cast_one]

/-- A common invertible measurable change of coordinates preserves the
affinity, using the pushed-forward reference measure on the target space.
In particular this applies to a common whitening or covariance transform. -/
theorem integral_product_dilation_map_equiv {E : Type*} [MeasurableSpace E]
    (e : (ι → ℝ) ≃ᵐ E) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {g : ℝ} (hg : 0 < g) :
    (∫ y, Real.sqrt (productDensity a (e.symm y)) *
      Real.sqrt (productDensity (fun i => a i / g) (e.symm y))
      ∂(Measure.map e volume)) =
      Cloning.Thermal.classicalBase g ^ ((Fintype.card ι : ℝ) / 2) := by
  rw [integral_map_equiv]
  simpa only [MeasurableEquiv.symm_apply_apply] using integral_product_dilation a ha hg

end Cloning.GaussianAffinity
