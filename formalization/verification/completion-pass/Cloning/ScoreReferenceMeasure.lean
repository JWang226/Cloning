import Cloning.PCTJointGaussianChart
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Whitening changes the intrinsic Lebesgue measure of the score hyperplane
by one strictly positive finite constant. That constant cancels exactly in
every normalized flat integral, independently of the integrand and window. -/
noncomputable section
open MeasureTheory
open scoped Topology BigOperators NNReal
namespace Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {A : Type*} [Fintype A] [LinearOrder A] {k : ℕ}

/-- The score hyperplane equipped with the ambient Euclidean inner product. -/
def euclideanScoreHyperplane (A : Type*) [Fintype A] :
    Submodule ℝ (EuclideanSpace ℝ A) :=
  (scoreHyperplane A).comap (WithLp.linearEquiv 2 ℝ (A → ℝ)).toLinearMap

/-- The identity on coordinates between Euclidean scores and the existing
score-space representation. -/
def intrinsicScoreEquiv : euclideanScoreHyperplane A ≃L[ℝ] scoreHyperplane A :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun h => ⟨WithLp.ofLp h.1, h.2⟩
      invFun := fun h => ⟨WithLp.toLp 2 h.1, h.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Intrinsic Euclidean volume on the trace-zero hyperplane, expressed in
the score coordinates used by the physical Gaussian experiment. -/
def intrinsicScoreMeasure : Measure (scoreHyperplane A) :=
  (volume : Measure (euclideanScoreHyperplane A)).map intrinsicScoreEquiv

instance intrinsicScoreMeasure_isAddHaarMeasure :
    Measure.IsAddHaarMeasure (intrinsicScoreMeasure (A := A)) :=
  (intrinsicScoreEquiv (A := A)).isAddHaarMeasure_map volume

instance scoreReferenceMeasure_isAddHaarMeasure (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) :
    Measure.IsAddHaarMeasure (scoreReferenceMeasure p hp b hb) :=
  (whiteningContinuousEquiv p hp b hb).symm.isAddHaarMeasure_map volume

/-- The Jacobian is a finite nonnegative real, and the following theorem
shows it is strictly positive. No Jacobian premise is supplied. -/
def scoreVolumeFactor (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) : ℝ≥0 :=
  Measure.addHaarScalarFactor (scoreReferenceMeasure p hp b hb) (intrinsicScoreMeasure (A := A))

theorem scoreVolumeFactor_pos (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) : 0 < scoreVolumeFactor p hp b hb :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem scoreReferenceMeasure_eq_intrinsic (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) :
    scoreReferenceMeasure p hp b hb = scoreVolumeFactor p hp b hb • (intrinsicScoreMeasure (A := A)) :=
  Measure.isAddLeftInvariant_eq_smul _ _

/-- The change from whitening volume to intrinsic hyperplane volume cancels
exactly in normalized averages, even for a nonrectangular score window. -/
theorem normalized_score_integral_eq_intrinsic (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (S : Set (scoreHyperplane A))
    (f : scoreHyperplane A → ℝ) :
    ((scoreReferenceMeasure p hp b hb).real S)⁻¹ *
        (∫ h in S, f h ∂scoreReferenceMeasure p hp b hb) =
      (intrinsicScoreMeasure.real S)⁻¹ * (∫ h in S, f h ∂intrinsicScoreMeasure) := by
  rw [scoreReferenceMeasure_eq_intrinsic, measureReal_nnreal_smul_apply,
    Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, mul_inv_rev]
  have hc : (scoreVolumeFactor p hp b hb : ℝ) ≠ 0 :=
    ne_of_gt (show (0:ℝ) < scoreVolumeFactor p hp b hb from
      scoreVolumeFactor_pos p hp b hb)
  calc
    _ = ((scoreVolumeFactor p hp b hb : ℝ)⁻¹ * scoreVolumeFactor p hp b hb) *
        ((intrinsicScoreMeasure.real S)⁻¹ * ∫ h in S, f h ∂intrinsicScoreMeasure) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc, one_mul]

end Cloning.PCTJointGaussianWhitening
