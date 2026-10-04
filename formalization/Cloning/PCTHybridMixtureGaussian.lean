import Cloning.PCTHybridMixtureFactor
import Cloning.PCTHybridMixtureClassical
import Cloning.PCTJointGaussianWhitenedLaw
import Cloning.PCTHybridFidelity

/-! Identification of the actual joint PCT tangent average with the literal
broadened Gaussian–thermal positive L1 field. The real chart is constructed
from the spectrum, and both laws and the operator-valued average are proved. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTHybridMixture
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTGaussianOutput Cloning.PCTJointGaussianLaw
open Cloning.PCTJointGaussianWhitening Cloning.PCTJointGaussianReal
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
open Cloning.GaussianAffinity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {k s d : ℕ}

/-- Exact joint L1 mixture in whitened physical coordinates. The seed has
classical covariance `I`, the tangent has covariance `2(g-1) I`, and the
output therefore has covariance `(2g-1) I`. -/
theorem tangent_hybrid_average_eq_pct_preparation
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) :
    let q : Fin d → ℝ := fun i => p (e i).1.2 / p (e i).1.1
    (∫ z, hybridTranslation (whitenedJointTangent u p b e z)
      (prepareL1 (productDensity (fun _ : Fin k => 1/2))
        (integrable_productDensity _ (fun _ => by norm_num))
        (vectorMixture (numberBasis d) (productGeometric q)))
        ∂gaussianProductMeasure (fun _ : Fin s => g-1)) =
      prepareL1 (productDensity (fun _ : Fin k => (1/2) / (2*g-1)))
        (integrable_productDensity _ (fun _ => div_pos (by norm_num) (by linarith)))
        (vectorMixture (numberBasis d) (productGeometric (fun i => Thermal.pct g (q i)))) := by
  dsimp only
  simp only [whitenedJointTangent]
  rw [tangent_hybrid_average_eq_classical_average u p hp hu hgap e g hg
    (whiten p b) (continuous_whiten p b) _ _ (productDensity_nonneg _)
    (integral_productDensity _ (fun _ => by norm_num))]
  let X := vectorMixture (numberBasis d)
    (productGeometric (fun i => Thermal.pct g (p (e i).1.2 / p (e i).1.1)))
  let C := prepareL1 (productDensity (fun _ : Fin k => 1/2))
    (integrable_productDensity _ (fun _ => by norm_num)) X
  change (∫ h, classicalTranslation (whiten p b h) C ∂classicalTangentLaw u p (g-1)) = _
  rw [← integral_map (continuous_whiten p b).aemeasurable
    (continuous_classicalTranslation C).aestronglyMeasurable,
    classicalTangentLaw_map_whiten u p hp hu b hb (sub_pos.mpr hg)]
  dsimp only [C]
  rw [gaussian_classical_translation_average _ _ (fun _ => by norm_num)
    (fun _ => div_pos zero_lt_one (mul_pos (by norm_num) (sub_pos.mpr hg)))]
  have ha : (fun _ : Fin k => (1/2 : ℝ) * (1 / (4 * (g-1))) /
      (1/2 + 1 / (4 * (g-1)))) = (fun _ : Fin k => (1/2 : ℝ) / (2*g-1)) := by
    funext i
    have h1 : g-1 ≠ 0 := ne_of_gt (sub_pos.mpr hg)
    have h2 : 2*g-1 ≠ 0 := by linarith
    have h3 : 0 < (1/2 : ℝ) + 1 / (4 * (g-1)) :=
      add_pos (by norm_num) (div_pos zero_lt_one (mul_pos (by norm_num) (sub_pos.mpr hg)))
    apply (div_eq_div_iff h3.ne' h2).mpr
    field_simp [h1]
    <;> ring
  simp only [ha, X]

/-- The actual tangent translation mixture is exactly the PCT comparison
state used by the literal fidelity formula. No target-mixture hypothesis is
assumed. Strict positivity and ordering are the current physical domain. -/
theorem tangent_hybrid_average_eq_pctGaussianThermalPositive
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (e : Fin d ≃ OrbitalPair A)
    (g : ℝ) (hg : 1 < g) :
    let q : Fin d → ℝ := fun i => p (e i).1.2 / p (e i).1.1
    let hq0 : ∀ i, 0 ≤ q i := fun i => (div_pos (hp _) (hp _)).le
    let hq1 : ∀ i, q i < 1 := fun i =>
      (div_lt_one (hp _)).mpr (by linarith [hgap _ _ (e i).2])
    (∫ z, hybridTranslation (whitenedJointTangent u p b e z)
      (gaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num) q hq0 hq1).1
      ∂gaussianProductMeasure (fun _ : Fin s => g-1)) =
      (pctGaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num)
        g hg q hq0 hq1).1 := by
  dsimp only [gaussianThermalPositive, pctGaussianThermalPositive,
    pctGaussianThermalField, PositiveField.toPositiveL1]
  simp_rw [gaussianThermalField_toL1]
  exact tangent_hybrid_average_eq_pct_preparation u p hp hu hgap b hb e g hg

end Cloning.PCTHybridMixture
