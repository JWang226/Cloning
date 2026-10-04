import Cloning.TensorLANEmbeddingClassicalCenter
import Cloning.PCTJointGaussianChart
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Actual whitening of the physical root-space density, with the Jacobian
derived from Haar measure and Gaussian normalization. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

/-- The existing PCT whitening coordinates applied to the literal Euclidean
root hyperplane. -/
def rootWhitening (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) : rootSpace d ≃L[ℝ] (Fin d → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => whiten p b x.1.ofLp
    invFun := fun y => ⟨WithLp.toLp 2 (unwhiten p b y), unwhiten_sum_zero p b hb y⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact congrArg (WithLp.toLp 2) (unwhiten_whiten p hp b hb x.1.ofLp x.2)
    right_inv := whiten_unwhiten p hp b
    map_add' := by
      intro x y
      funext i
      simp [whiten, mul_add, add_div, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      funext i
      simp [whiten, Finset.mul_sum, mul_div_assoc, mul_assoc, mul_left_comm] }

@[simp] theorem rootWhitening_apply (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (x : rootSpace d) :
    rootWhitening p hp b hb x = whiten p b x.1.ofLp := rfl

/-- The whitening chart has precisely the reciprocal-covariance quadratic
form, including its normalization and its trace-zero restriction. -/
theorem rootWhitening_norm_sq (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p) (x : rootSpace d) :
    (∑ i, (rootWhitening p hp b hb x i)^2) = ∑ a, (x.1 a)^2 / p a := by
  rw [rootWhitening_apply, ← whiteningVector_norm_sq b (whiten p b x.1.ofLp),
    whiteningVector_whiten p hp b hb x.1.ofLp x.2, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro a _
  simp only [normalizedScore, WithLp.ofLp_toLp, div_pow, Real.sq_sqrt (hp a).le]

section DensityTransport
variable (W : rootSpace d ≃L[ℝ] (Fin d → ℝ))

def whiteningJacobian : ℝ≥0 :=
  Measure.addHaarScalarFactor ((volume : Measure (rootSpace d)).map W) (volume : Measure (Fin d → ℝ))

theorem whiteningJacobian_pos : 0 < whiteningJacobian W :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem rootWhitening_map_volume :
    (volume : Measure (rootSpace d)).map W = whiteningJacobian W • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

/-- Push a density to coordinate Lebesgue measure, including its actual
positive Jacobian. -/
def whiteningDensity (f : rootSpace d → ℝ) (y : Fin d → ℝ) : ℝ :=
  (whiteningJacobian W : ℝ) * f (W.symm y)

theorem whiteningDensity_integral (f : rootSpace d → ℝ) :
    (∫ y, whiteningDensity W f y) = ∫ x, f x := by
  have h := integral_map_equiv (μ := (volume : Measure (rootSpace d)))
    W.toHomeomorph.toMeasurableEquiv (fun y => f (W.symm y))
  change (∫ y, f (W.symm y) ∂((volume : Measure (rootSpace d)).map W)) =
    (∫ x, f (W.symm (W x))) at h
  rw [rootWhitening_map_volume, integral_smul_nnreal_measure] at h
  simpa only [whiteningDensity, integral_const_mul, NNReal.smul_def,
    ContinuousLinearEquiv.symm_apply_apply] using h

theorem whiteningDensity_integrable (f : rootSpace d → ℝ) (hf : Integrable f) :
    Integrable (whiteningDensity W f) := by
  have hi : Integrable (fun y => f (W.symm y))
      ((volume : Measure (rootSpace d)).map W) := by
    apply (integrable_map_equiv W.toHomeomorph.toMeasurableEquiv _).mpr
    change Integrable (fun x => f (W.symm (W x)))
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf
  rw [rootWhitening_map_volume] at hi
  change Integrable (fun y => f (W.symm y))
    ((whiteningJacobian W : ℝ≥0∞) • volume) at hi
  have hj := (whiteningJacobian_pos W).ne'
  have hi' := (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hj)
    ENNReal.coe_ne_top).mp hi
  exact hi'.const_mul _

theorem whiteningDensity_l1 (f g : rootSpace d → ℝ) :
    (∫ y, |whiteningDensity W f y - whiteningDensity W g y|) =
      ∫ x, |f x - g x| := by
  have h := whiteningDensity_integral W (fun x => |f x - g x|)
  simpa only [whiteningDensity, ← mul_sub, abs_mul,
    abs_of_nonneg (NNReal.coe_nonneg (whiteningJacobian W))] using h

end DensityTransport

end Cloning.TensorLAN
