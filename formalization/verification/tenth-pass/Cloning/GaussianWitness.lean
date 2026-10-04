import Cloning.GaussianAffinity
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Concrete classical Gaussian witnesses

The density-ratio witness in the hybrid converse is an actual bounded positive
function. Its inverse moment and its translated Gaussian moment are evaluated
by Lebesgue integration, rather than imposed as model assumptions.
-/

noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace Cloning.GaussianAffinity

theorem density_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < density a x := by
  unfold density
  positivity

theorem continuous_density (a : ℝ) : Continuous (density a) := by
  unfold density
  fun_prop

/-- Square root of the ratio of the narrow and broad Gaussian densities. -/
def witness (a b x : ℝ) : ℝ := Real.sqrt (density a x) / Real.sqrt (density b x)

theorem witness_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 < witness a b x :=
  div_pos (Real.sqrt_pos.mpr (density_pos ha x)) (Real.sqrt_pos.mpr (density_pos hb x))

theorem continuous_witness {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (witness a b) :=
  (continuous_density a).sqrt.div (continuous_density b).sqrt
    (fun x => (Real.sqrt_pos.mpr (density_pos hb x)).ne')

theorem witness_closed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    witness a b x = Real.sqrt (Real.sqrt a / Real.sqrt b) *
      Real.exp (-((a - b) / 2) * x ^ 2) := by
  unfold witness
  rw [sqrt_density, sqrt_density, mul_div_mul_comm,
    ← Real.sqrt_div (by positivity : 0 ≤ Real.sqrt a / Real.sqrt Real.pi),
    ← Real.exp_sub]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hratio : (Real.sqrt a / Real.sqrt Real.pi) /
      (Real.sqrt b / Real.sqrt Real.pi) = Real.sqrt a / Real.sqrt b := by
    field_simp
  rw [hratio]
  congr 2
  ring

theorem witness_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (x : ℝ) :
    witness a b x ≤ Real.sqrt (Real.sqrt a / Real.sqrt b) := by
  rw [witness_closed ha hb]
  apply mul_le_of_le_one_right (Real.sqrt_nonneg _)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x))

theorem density_div_witness {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    density a x / witness a b x =
      Real.sqrt (density a x) * Real.sqrt (density b x) := by
  unfold witness
  have hsa : Real.sqrt (density a x) ≠ 0 := (Real.sqrt_pos.mpr (density_pos ha x)).ne'
  have hsb : Real.sqrt (density b x) ≠ 0 := (Real.sqrt_pos.mpr (density_pos hb x)).ne'
  field_simp
  rw [Real.sq_sqrt (density_nonneg a x)]

theorem integrable_affinity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x => Real.sqrt (density a x) * Real.sqrt (density b x)) := by
  have heq (x : ℝ) : Real.sqrt (density a x) * Real.sqrt (density b x) =
      (Real.sqrt (Real.sqrt a / Real.sqrt Real.pi) *
        Real.sqrt (Real.sqrt b / Real.sqrt Real.pi)) *
        Real.exp (-((a + b) / 2) * x ^ 2) := by
    rw [sqrt_density, sqrt_density, mul_mul_mul_comm, ← Real.exp_add]
    congr 2
    ring
  simp_rw [heq]
  exact (integrable_exp_neg_mul_sq (by positivity : 0 < (a + b) / 2)).const_mul _

theorem integrable_density_div_witness {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x => density a x / witness a b x) := by
  simp_rw [density_div_witness ha hb]
  exact integrable_affinity ha hb

theorem integral_density_div_witness {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, density a x / witness a b x) =
      Real.sqrt (2 * Real.sqrt a * Real.sqrt b / (a + b)) := by
  simp_rw [density_div_witness ha hb]
  exact integral_sqrt_density_mul ha hb

/-- Completing the square with an arbitrary translation and linear gain. -/
theorem integral_gaussian_translate {a c r v : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    (∫ h : ℝ, Real.exp (-a * h ^ 2 - c * (v + r * h) ^ 2)) =
      Real.exp (-(a * c / (a + c * r ^ 2)) * v ^ 2) *
        Real.sqrt (Real.pi / (a + c * r ^ 2)) := by
  have hA : 0 < a + c * r ^ 2 := add_pos_of_pos_of_nonneg ha (mul_nonneg hc (sq_nonneg r))
  have heq (h : ℝ) : -a * h ^ 2 - c * (v + r * h) ^ 2 =
      -(a * c / (a + c * r ^ 2)) * v ^ 2 +
        -(a + c * r ^ 2) * (h + c * r * v / (a + c * r ^ 2)) ^ 2 := by
    field_simp
    <;> ring
  simp_rw [heq, Real.exp_add]
  rw [integral_const_mul,
    integral_add_right_eq_self (fun h : ℝ => Real.exp (-(a + c * r ^ 2) * h ^ 2)),
    integral_gaussian]

theorem witness_dilation_closed {a g : ℝ} (ha : 0 < a) (hg : 0 < g) (x : ℝ) :
    witness a (a / g) x = Real.sqrt (Real.sqrt g) *
      Real.exp (-((a - a / g) / 2) * x ^ 2) := by
  rw [witness_closed ha (div_pos ha hg), Real.sqrt_div ha.le]
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hr : Real.sqrt a / (Real.sqrt a / Real.sqrt g) = Real.sqrt g := by
    field_simp
  rw [hr]

theorem dilation_prefactor {a g : ℝ} (ha : 0 < a) (hg : 1 ≤ g) :
    Real.sqrt (Real.sqrt g) * (Real.sqrt a / Real.sqrt Real.pi) *
      Real.sqrt (Real.pi / (a + (a - a / g) / 2 * (Real.sqrt g) ^ 2)) =
      Real.sqrt (Cloning.Thermal.classicalBase g) := by
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hc : 0 ≤ (a - a / g) / 2 := by
    have : a / g ≤ a := (div_le_iff₀ hg0).mpr (by nlinarith)
    linarith
  have hA : 0 < a + (a - a / g) / 2 * (Real.sqrt g) ^ 2 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have heq : a + (a - a / g) / 2 * (Real.sqrt g) ^ 2 = a * (1 + g) / 2 := by
    rw [Real.sq_sqrt hg0.le]
    field_simp
    <;> ring
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (Real.sqrt_nonneg g),
    Real.sq_sqrt ha.le, Real.sq_sqrt Real.pi_pos.le,
    Real.sq_sqrt (div_pos Real.pi_pos hA).le,
    Real.sq_sqrt (Cloning.Thermal.classicalBase_pos hg0).le, heq]
  unfold Cloning.Thermal.classicalBase
  field_simp
  <;> ring

/-- The classical translation identity used to bound the weighted output mass. -/
theorem integral_density_translated_witness {a g : ℝ}
    (ha : 0 < a) (hg : 1 ≤ g) (v : ℝ) :
    (∫ h : ℝ, density a h * witness a (a / g) (v + Real.sqrt g * h)) =
      Real.sqrt (Cloning.Thermal.classicalBase g) *
        Real.exp (-(a * (g - 1) / (g * (1 + g))) * v ^ 2) := by
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hc : 0 ≤ (a - a / g) / 2 := by
    have : a / g ≤ a := (div_le_iff₀ hg0).mpr (by nlinarith)
    linarith
  have heq (h : ℝ) : density a h * witness a (a / g) (v + Real.sqrt g * h) =
      (Real.sqrt (Real.sqrt g) * (Real.sqrt a / Real.sqrt Real.pi)) *
      Real.exp (-a * h ^ 2 - (a - a / g) / 2 * (v + Real.sqrt g * h) ^ 2) := by
    rw [witness_dilation_closed ha hg0, density]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    ring_nf
  simp_rw [heq]
  rw [integral_const_mul, integral_gaussian_translate ha hc]
  rw [← mul_assoc, mul_right_comm _ (Real.exp _), dilation_prefactor ha hg]
  congr 2
  rw [Real.sq_sqrt hg0.le]
  have hA : a + (a - a / g) / 2 * g = a * (1 + g) / 2 := by
    field_simp
    <;> ring
  rw [hA]
  field_simp
  <;> ring

theorem integral_density_translated_witness_le {a g : ℝ}
    (ha : 0 < a) (hg : 1 ≤ g) (v : ℝ) :
    (∫ h : ℝ, density a h * witness a (a / g) (v + Real.sqrt g * h)) ≤
      Real.sqrt (Cloning.Thermal.classicalBase g) := by
  rw [integral_density_translated_witness ha hg]
  apply mul_le_of_le_one_right (Real.sqrt_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
    (div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hg)) (by positivity))) (sq_nonneg v)

variable {ι : Type*} [Fintype ι]

def productWitness (a b : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, witness (a i) (b i) (x i)

theorem integrable_productDensity (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (productDensity a) :=
  Integrable.fintype_prod (fun i => integrable_density (ha i))

theorem productWitness_pos (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (x : ι → ℝ) : 0 < productWitness a b x :=
  Finset.prod_pos (fun i _ => witness_pos (ha i) (hb i) (x i))

theorem continuous_productWitness (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) : Continuous (productWitness a b) := by
  unfold productWitness
  exact continuous_finset_prod _ (fun i _ => (continuous_witness (ha i) (hb i)).comp
    (continuous_apply i))

theorem productWitness_le (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hba : ∀ i, b i ≤ a i) (x : ι → ℝ) :
    productWitness a b x ≤ ∏ i, Real.sqrt (Real.sqrt (a i) / Real.sqrt (b i)) :=
  Finset.prod_le_prod (fun i _ => (witness_pos (ha i) (hb i) (x i)).le)
    (fun i _ => witness_le (ha i) (hb i) (hba i) (x i))

theorem integrable_productDensity_div_witness (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Integrable (fun x => productDensity a x / productWitness a b x) := by
  simp_rw [productDensity, productWitness, ← Finset.prod_div_distrib]
  exact Integrable.fintype_prod (fun i => integrable_density_div_witness (ha i) (hb i))

theorem integral_productDensity_div_witness (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {g : ℝ} (hg : 0 < g) :
    (∫ x, productDensity a x / productWitness a (fun i => a i / g) x) =
      Cloning.Thermal.classicalBase g ^ ((Fintype.card ι : ℝ) / 2) := by
  have heq (x : ι → ℝ) :
      productDensity a x / productWitness a (fun i => a i / g) x =
      Real.sqrt (productDensity a x) * Real.sqrt (productDensity (fun i => a i / g) x) := by
    simp only [productDensity, productWitness, ← Finset.prod_div_distrib]
    simp_rw [density_div_witness (ha _) (div_pos (ha _) hg)]
    rw [Finset.prod_mul_distrib, Real.sqrt_prod _ (fun i _ => density_nonneg _ _),
      Real.sqrt_prod _ (fun i _ => density_nonneg _ _)]
  simp_rw [heq]
  exact integral_product_dilation a ha hg

theorem integrable_translated_witness {a g : ℝ}
    (ha : 0 < a) (hg : 1 ≤ g) (v : ℝ) :
    Integrable (fun h : ℝ => density a h * witness a (a / g) (v + Real.sqrt g * h)) := by
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hba : a / g ≤ a := (div_le_iff₀ hg0).mpr (by nlinarith)
  apply (integrable_density ha).mul_bdd
    (((continuous_witness ha (div_pos ha hg0)).comp (by fun_prop)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun h => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_pos (witness_pos ha (div_pos ha hg0) _)]
    exact witness_le ha (div_pos ha hg0) hba _

theorem integrable_product_translated_witness (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {g : ℝ} (hg : 1 ≤ g) (v : ι → ℝ) :
    Integrable (fun h : ι → ℝ => productDensity a h *
      productWitness a (fun i => a i / g) (fun i => v i + Real.sqrt g * h i)) := by
  simp only [productDensity, productWitness, ← Finset.prod_mul_distrib]
  exact Integrable.fintype_prod (fun i => integrable_translated_witness (ha i) hg (v i))

/-- The sharp Gaussian translation bound in every finite classical dimension,
including the zero-dimensional register. -/
theorem integral_product_translated_witness_le (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {g : ℝ} (hg : 1 ≤ g) (v : ι → ℝ) :
    (∫ h : ι → ℝ, productDensity a h *
      productWitness a (fun i => a i / g) (fun i => v i + Real.sqrt g * h i)) ≤
      Cloning.Thermal.classicalBase g ^ ((Fintype.card ι : ℝ) / 2) := by
  simp only [productDensity, productWitness, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i t => density (a i) t * witness (a i) (a i / g) (v i + Real.sqrt g * t))]
  calc
    _ ≤ ∏ _i : ι, Real.sqrt (Cloning.Thermal.classicalBase g) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg fun h => mul_nonneg (density_nonneg _ _)
          (witness_pos (ha i) (div_pos (ha i) (lt_of_lt_of_le zero_lt_one hg)) _).le
      · intro i _
        exact integral_density_translated_witness_le (ha i) hg (v i)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, Real.sqrt_eq_rpow,
        ← Real.rpow_mul_natCast (Cloning.Thermal.classicalBase_pos
          (lt_of_lt_of_le zero_lt_one hg)).le]
      congr 1
      ring

end Cloning.GaussianAffinity
