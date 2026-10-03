import Cloning.WeylIrreducibleGaussian

/-! A Gaussian vector integral of the constructed Weyl representation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.ComplexCoherent
open Cloning.CoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def weylGaussianWeight (a : ℂ) : ℝ := Real.exp (-‖a‖ ^ 2 / 2) / Real.pi

lemma weylGaussianWeight_eq (a : ℂ) :
    weylGaussianWeight a = 2 * gaussianDensity 2 a := by
  simp only [weylGaussianWeight, gaussianDensity]
  ring

lemma weylGaussianWeight_nonneg (a : ℂ) : 0 ≤ weylGaussianWeight a := by
  unfold weylGaussianWeight
  positivity

lemma continuous_weylGaussianWeight : Continuous weylGaussianWeight := by
  unfold weylGaussianWeight
  fun_prop

lemma integrable_weylGaussianWeight : Integrable weylGaussianWeight := by
  change Integrable (fun a ↦ weylGaussianWeight a)
  simp_rw [weylGaussianWeight_eq]
  exact (integrable_gaussianDensity (s := 2) (by norm_num)).const_mul 2

lemma integral_weylGaussianWeight : (∫ a : ℂ, weylGaussianWeight a) = 2 := by
  simp_rw [weylGaussianWeight_eq]
  rw [integral_const_mul, gaussianDensity_integral (by norm_num), mul_one]

lemma integrable_weighted_displacement (v : Fock) :
    Integrable (fun a : ℂ ↦ (weylGaussianWeight a : ℂ) • displacement a v) := by
  apply (integrable_weylGaussianWeight.mul_const ‖v‖).mono'
    ((Complex.continuous_ofReal.comp continuous_weylGaussianWeight).smul
      (continuous_displacement v)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a ↦ by
    simp only [Function.comp_apply]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weylGaussianWeight_nonneg a), displacement_norm])

/-- The strong Gaussian integral is taken separately on each Fock vector;
operator-norm measurability of Weyl operators is unnecessary. -/
def weylGaussianVector (v : Fock) : Fock :=
  ∫ a : ℂ, (weylGaussianWeight a : ℂ) • displacement a v

lemma weylGaussianVector_norm (v : Fock) : ‖weylGaussianVector v‖ ≤ 2 * ‖v‖ := by
  unfold weylGaussianVector
  calc
    _ ≤ ∫ a : ℂ, ‖(weylGaussianWeight a : ℂ) • displacement a v‖ := norm_integral_le_integral_norm _
    _ = ∫ a : ℂ, weylGaussianWeight a * ‖v‖ := by
      congr 1
      funext a
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weylGaussianWeight_nonneg a), displacement_norm]
    _ = _ := by rw [integral_mul_const, integral_weylGaussianWeight]

def weylGaussianAverage : Fock →L[ℂ] Fock :=
  ({ toFun := weylGaussianVector
     map_add' := by
       intro v w
       simp only [weylGaussianVector, map_add, smul_add]
       exact integral_add (integrable_weighted_displacement v) (integrable_weighted_displacement w)
     map_smul' := by
       intro c v
       simp only [weylGaussianVector, map_smul, smul_comm (weylGaussianWeight _ : ℂ) c,
         integral_smul, RingHom.id_apply] } : Fock →ₗ[ℂ] Fock).mkContinuous 2 weylGaussianVector_norm

@[simp] lemma weylGaussianAverage_apply (v : Fock) :
    weylGaussianAverage v = ∫ a : ℂ, (weylGaussianWeight a : ℂ) • displacement a v := rfl

end Cloning.ComplexCoherent
