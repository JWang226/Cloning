import Cloning.PCTJointGaussianLaw
import Cloning.PCTJointGaussianReal
import Cloning.PCTJointGaussianWhitening

/-! The explicit real whitening chart sends the actual classical tangent
law to the Gaussian of covariance `2v I`. Together with the orbital law this
identifies the entire joint distribution, without an independence premise. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.PCTJointGaussianWhitening
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTGaussianOutput Cloning.PCTJointGaussianLaw
open Cloning.PCTJointGaussianReal Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [LinearOrder A] {k s d : ℕ}

theorem classicalTangentLaw_map_whiten
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) {v : ℝ} (hv : 0 < v) :
    (classicalTangentLaw u p v).map (whiten p b) =
      realProductMeasure (fun _ : Fin k => 1 / (4 * v)) := by
  letI := classicalTangentLaw_probability u p hv
  letI := Measure.isProbabilityMeasure_map (μ := classicalTangentLaw u p v)
    (continuous_whiten p b).aemeasurable
  apply eq_realProductMeasure_of_characteristic hv
  intro t
  have hc : Continuous (fun x : Fin k → ℝ =>
      Complex.exp (Complex.I * ((∑ i, t i * x i : ℝ) : ℂ))) := by fun_prop
  rw [integral_map (continuous_whiten p b).aemeasurable hc.aestronglyMeasurable]
  unfold classicalTangentLaw
  have hi := integral_map (μ := gaussianProductMeasure (fun _ : Fin s => v))
    (continuous_tangentClassical u p).aemeasurable
    (hc.comp (continuous_whiten p b)).aestronglyMeasurable
  dsimp only [Function.comp_def] at hi
  rw [hi]
  exact whitenedClassical_characteristic u p hp hu b hb hv t

def whitenedJointTangent (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (b : Fin (k + 1) → EuclideanSpace ℝ A) (e : Fin d ≃ OrbitalPair A)
    (z : Fin s → ℂ) : (Fin k → ℝ) × (Fin d → ℂ) :=
  (whiten p b (tangentClassical u p z), tangentDisplacement u p e z)

theorem continuous_whitenedJointTangent (u : Fin (s + 1) → Register (A × A))
    (p : A → ℝ) (b : Fin (k + 1) → EuclideanSpace ℝ A)
    (e : Fin d ≃ OrbitalPair A) : Continuous (whitenedJointTangent u p b e) :=
  ((continuous_whiten p b).comp (continuous_tangentClassical u p)).prodMk
    (continuous_tangentDisplacement u p e)

/-- Exact joint Gaussian law of the physical differential in the constructed
whitening coordinates. The first factor has covariance `2v I`; orbital
variances are the physically derived spectrum ratios. -/
theorem whitenedJointTangent_map_eq_prod
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (e : Fin d ≃ OrbitalPair A)
    {v : ℝ} (hv : 0 < v) :
    (gaussianProductMeasure (fun _ : Fin s => v)).map (whitenedJointTangent u p b e) =
      (realProductMeasure (fun _ : Fin k => 1 / (4 * v))).prod
        (gaussianProductMeasure (orbitalVariance p e v)) := by
  letI := classicalTangentLaw_probability u p hv
  letI := gaussianProductMeasure_probability (orbitalVariance_pos p hp hgap e hv)
  rw [← classicalTangentLaw_map_whiten u p hp hu b hb hv]
  have hm := Measure.map_prod_map (classicalTangentLaw u p v)
    (gaussianProductMeasure (orbitalVariance p e v))
    (continuous_whiten p b).measurable measurable_id
  rw [Measure.map_id] at hm
  rw [hm, ← jointTangent_map_eq_prod u p hp hu hgap e hv,
    Measure.map_map ((continuous_whiten p b).measurable.prodMap measurable_id)
      (continuous_jointTangent u p e).measurable]
  rfl

end Cloning.PCTJointGaussianWhitening
