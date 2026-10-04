import Cloning.PCTJointGaussianWhitenedLaw
import Cloning.HybridCoordinateTransport
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! A concrete equivalence between the trace-zero classical score hyperplane
and whitening coordinates. Its reference measure is explicitly the pullback
of coordinate Lebesgue measure; no unproved intrinsic-volume Jacobian is used. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.PCTJointGaussianWhitening
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTJointGaussianLaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {k : ℕ}

def scoreHyperplane (A : Type*) [Fintype A] : Submodule ℝ (A → ℝ) where
  carrier := {h | ∑ a, h a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro h j hh hj
    change ∑ a, h a = 0 at hh
    change ∑ a, j a = 0 at hj
    change ∑ a, (h a + j a) = 0
    simp [Finset.sum_add_distrib, hh, hj]
  smul_mem' := by
    intro c h hh
    change ∑ a, h a = 0 at hh
    change ∑ a, c * h a = 0
    rw [← Finset.mul_sum, hh, mul_zero]

def normalizedScore (p : A → ℝ) (h : A → ℝ) : EuclideanSpace ℝ A :=
  WithLp.toLp 2 (fun a => h a / Real.sqrt (p a))

def unwhiten (p : A → ℝ) (b : Fin (k+1) → EuclideanSpace ℝ A)
    (x : Fin k → ℝ) : A → ℝ :=
  fun a => Real.sqrt (p a) * whiteningVector b x a

theorem unwhiten_sum_zero (p : A → ℝ)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (x : Fin k → ℝ) :
    ∑ a, unwhiten p b x a = 0 := by
  have h := whiteningVector_orthogonal b x
  rw [hb, EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct, sqrtSpectrum, unwhiten, mul_comm] using h

theorem whiten_eq_inner (p : A → ℝ)
    (b : Fin (k+1) → EuclideanSpace ℝ A) (h : A → ℝ) (i : Fin k) :
    whiten p b h i = ⟪b i.succ, normalizedScore p h⟫_ℝ := by
  simp only [whiten, normalizedScore, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem normalizedScore_unwhiten (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : Fin (k+1) → EuclideanSpace ℝ A) (x : Fin k → ℝ) :
    normalizedScore p (unwhiten p b x) = whiteningVector b x := by
  ext a
  simp only [normalizedScore, WithLp.ofLp_toLp, unwhiten]
  field_simp [(Real.sqrt_pos.mpr (hp a)).ne']

theorem whiten_unwhiten (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A)) (x : Fin k → ℝ) :
    whiten p b (unwhiten p b x) = x := by
  funext i
  rw [whiten_eq_inner, normalizedScore_unwhiten p hp]
  simp [whiteningVector, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]

theorem normalizedScore_inner_zero (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (h : A → ℝ) :
    ⟪b 0, normalizedScore p h⟫_ℝ = ∑ a, h a := by
  rw [hb, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, sqrtSpectrum, normalizedScore, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro a _
  field_simp [(Real.sqrt_pos.mpr (hp a)).ne']

theorem whiteningVector_whiten (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (h : A → ℝ) (hh : ∑ a, h a = 0) :
    whiteningVector b (whiten p b h) = normalizedScore p h := by
  have hs := b.sum_repr' (normalizedScore p h)
  rw [Fin.sum_univ_succ, normalizedScore_inner_zero p hp b hb, hh, zero_smul, zero_add] at hs
  simpa only [whiteningVector, whiten_eq_inner] using hs

theorem unwhiten_whiten (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (h : A → ℝ) (hh : ∑ a, h a = 0) :
    unwhiten p b (whiten p b h) = h := by
  funext a
  rw [unwhiten, whiteningVector_whiten p hp b hb h hh]
  simp only [normalizedScore, WithLp.ofLp_toLp]
  field_simp [(Real.sqrt_pos.mpr (hp a)).ne']

/-- Explicit linear equivalence on the actual trace-zero score space. -/
def whiteningEquiv (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) : scoreHyperplane A ≃ₗ[ℝ] (Fin k → ℝ) where
  toFun h := whiten p b h.1
  invFun x := ⟨unwhiten p b x, unwhiten_sum_zero p b hb x⟩
  left_inv h := Subtype.ext (unwhiten_whiten p hp b hb h.1 h.2)
  right_inv := whiten_unwhiten p hp b
  map_add' h j := by
    funext i
    simp [whiten, mul_add, add_div, Finset.sum_add_distrib]
  map_smul' c h := by
    funext i
    simp [whiten, Finset.mul_sum, mul_div_assoc, mul_assoc, mul_left_comm]

def whiteningContinuousEquiv (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) : scoreHyperplane A ≃L[ℝ] (Fin k → ℝ) :=
  (whiteningEquiv p hp b hb).toContinuousLinearEquiv

def whiteningMeasurableEquiv (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) : scoreHyperplane A ≃ᵐ (Fin k → ℝ) :=
  (whiteningContinuousEquiv p hp b hb).toHomeomorph.toMeasurableEquiv

@[simp] theorem whiteningMeasurableEquiv_apply (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (h : scoreHyperplane A) :
    whiteningMeasurableEquiv p hp b hb h = whiten p b h.1 := rfl

@[simp] theorem whiteningMeasurableEquiv_symm_apply (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (x : Fin k → ℝ) :
    ((whiteningMeasurableEquiv p hp b hb).symm x).1 = unwhiten p b x := rfl

/-- The reference measure on physical scores associated to this chart. -/
def scoreReferenceMeasure (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) : Measure (scoreHyperplane A) :=
  volume.map (whiteningMeasurableEquiv p hp b hb).symm

theorem whitening_measurePreserving (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) :
    MeasurePreserving (whiteningMeasurableEquiv p hp b hb)
      (scoreReferenceMeasure p hp b hb) volume := by
  refine ⟨(whiteningMeasurableEquiv p hp b hb).measurable, ?_⟩
  exact (whiteningMeasurableEquiv p hp b hb).map_map_symm

/-- The concrete score chart transports every genuine hybrid competitor. -/
def scoreChannelEquiv {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) :
    Hybrid.Channel H K (scoreReferenceMeasure p hp b hb) ≃
      Hybrid.Channel H K (volume : Measure (Fin k → ℝ)) :=
  Hybrid.Channel.coordinateEquiv (whiteningMeasurableEquiv p hp b hb)
    (whitening_measurePreserving p hp b hb)

theorem continuous_unwhiten (p : A → ℝ) (b : Fin (k+1) → EuclideanSpace ℝ A) :
    Continuous (unwhiten p b) := by
  unfold unwhiten whiteningVector
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  fun_prop

section PhysicalLaw
variable {s : ℕ}
open Cloning.MultimodeCoherentGaussianMixture Cloning.PCTJointGaussianReal

theorem tangentClassical_sum_zero
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hu : u 0 = coefficientVector (schmidtCoefficients p)) (z : Fin s → ℂ) :
    ∑ a, tangentClassical u p z a = 0 := by
  apply classicalCoordinate_sum_zero
  rw [coefficientVector_frameTangentMatrix, ← hu]
  exact frameTangent_orthogonal u.orthonormal z

/-- The singular physical classical law is the image of the nonsingular
Gaussian under the explicit inverse chart, not a stipulated covariance law. -/
theorem classicalTangentLaw_eq_unwhiten_map
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) {v : ℝ} (hv : 0 < v) :
    classicalTangentLaw u p v =
      (realProductMeasure (fun _ : Fin k => 1 / (4*v))).map (unwhiten p b) := by
  rw [← classicalTangentLaw_map_whiten u p hp hu b hb hv]
  unfold classicalTangentLaw
  rw [Measure.map_map (continuous_whiten p b).measurable (continuous_tangentClassical u p).measurable,
    Measure.map_map (continuous_unwhiten p b).measurable
      ((continuous_whiten p b).comp (continuous_tangentClassical u p)).measurable]
  congr 1
  funext z
  exact (unwhiten_whiten p hp b hb _ (tangentClassical_sum_zero u p hu z)).symm

end PhysicalLaw

end Cloning.PCTJointGaussianWhitening
