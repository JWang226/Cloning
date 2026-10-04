import Cloning.PCTTangentChart
import Cloning.PCTGaussianCovarianceJoint

/-! The actual exponential chart in the manuscript's spectral and orbital
coordinates, together with the coordinate limit for normalized tangents. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
open Matrix NormedSpace Filter
namespace Cloning.PCTLocalChart
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A]

def spectralCoordinates (H : Hermitian A) : A → ℝ := fun a => (H.val a a).re

def orbitalCoordinates (p : A → ℝ) (H : Hermitian A) : OrbitalPair A → ℂ :=
  fun ij => H.val ij.1.2 ij.1.1 / (Real.sqrt (p ij.1.1 - p ij.1.2) : ℂ)

lemma continuous_spectralCoordinates : Continuous (spectralCoordinates (A := A)) := by
  apply continuous_pi
  intro a
  have he : Continuous (fun M : Matrix A A ℂ => M a a) :=
    (continuous_apply a).comp (continuous_apply a)
  exact (Complex.continuous_re.comp he).comp (inclusion (A := A)).continuous

lemma continuous_orbitalCoordinates (p : A → ℝ) : Continuous (orbitalCoordinates p) := by
  apply continuous_pi
  intro ij
  exact (((continuous_apply ij.1.1).comp (continuous_apply ij.1.2)).comp
    (inclusion (A := A)).continuous).div_const _

lemma diagonalPart_eq_spectralCoordinates (H : Hermitian A) :
    diagonalPart H.val = Matrix.diagonal (fun a => (spectralCoordinates H a : ℂ)) := by
  change Matrix.diagonal (fun a => H.val a a) = _
  congr 1
  funext a
  have hh := congrArg (fun M : Matrix A A ℂ => M a a) H.2
  exact (Complex.conj_eq_iff_re.mp hh).symm

/-- The literal zero-diagonal skew generator in ordered orbital coordinates. -/
def orbitalGenerator (p : A → ℝ) (z : OrbitalPair A → ℂ) : Matrix A A ℂ :=
  fun a b => if hab : a < b then -star (z ⟨(a,b),hab⟩) / (Real.sqrt (p a - p b) : ℂ)
    else if hba : b < a then z ⟨(b,a),hba⟩ / (Real.sqrt (p b - p a) : ℂ) else 0

lemma generator_lower (p : A → ℝ) (H : Hermitian A) (i j : A) (hij : i < j)
    (hgap : 0 < p i - p j) :
    generator p H j i = orbitalCoordinates p H ⟨(i,j),hij⟩ /
      (Real.sqrt (p i - p j) : ℂ) := by
  simp only [generator_apply, if_neg (ne_of_gt hij), orbitalCoordinates]
  rw [div_div]
  congr 1
  exact_mod_cast (Real.mul_self_sqrt hgap.le).symm

lemma generator_upper (p : A → ℝ) (H : Hermitian A) (i j : A) (hij : i < j)
    (hgap : 0 < p i - p j) :
    generator p H i j = -star (orbitalCoordinates p H ⟨(i,j),hij⟩) /
      (Real.sqrt (p i - p j) : ℂ) := by
  have hh := congrArg (fun M : Matrix A A ℂ => M i j) H.2
  change (starRingEnd ℂ) (H.val j i) = H.val i j at hh
  simp only [generator_apply, if_neg (ne_of_lt hij), orbitalCoordinates, star_div₀,
    Complex.star_def, Complex.conj_ofReal, hh, neg_div, div_div]
  have hs : (Real.sqrt (p i - p j) : ℂ) * (Real.sqrt (p i - p j) : ℂ) =
      ((p i - p j : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt hgap.le
  rw [hs]
  rw [show ((p j - p i : ℝ) : ℂ) = -((p i - p j : ℝ) : ℂ) by push_cast; ring, div_neg]

/-- The Hermitian-coordinate generator is exactly the manuscript generator. -/
theorem generator_eq_orbitalGenerator (p : A → ℝ)
    (hgap : ∀ i j, i < j → 0 < p i - p j) (H : Hermitian A) :
    generator p H = orbitalGenerator p (orbitalCoordinates p H) := by
  ext a b
  by_cases hab : a < b
  · simpa only [orbitalGenerator, dif_pos hab] using generator_upper p H a b hab (hgap a b hab)
  · by_cases hba : b < a
    · simpa only [orbitalGenerator, dif_neg hab, dif_pos hba] using
        generator_lower p H b a hba (hgap b a hba)
    · have he : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
      subst b
      simp [orbitalGenerator]

/-- The spectral coordinate limit equals the actual partial-trace diagonal. -/
theorem scaledSpectralCoordinates_tendsto (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    Tendsto (fun t : ℝ => spectralCoordinates (t⁻¹ • tangentCoordinates p hp Z t)) (𝓝[≠] 0)
      (𝓝 (classicalCoordinate p Z)) := by
  have h := continuous_spectralCoordinates.continuousAt.tendsto.comp
    (scaledTangentCoordinates_tendsto p hp Z)
  have he : spectralCoordinates (tangentDifferential p Z) = classicalCoordinate p Z := by
    funext a
    simp [spectralCoordinates, tangentDifferential, partialTraceDifferential_diagonal,
      classicalCoordinate]
  rw [he] at h
  exact h

/-- The orbital limit equals the actual Gaussian tangent displacement. -/
theorem scaledOrbitalCoordinates_tendsto (p : A → ℝ) (hp : Function.Injective p)
    (Z : Matrix A A ℂ) :
    Tendsto (fun t : ℝ => orbitalCoordinates p (t⁻¹ • tangentCoordinates p hp Z t)) (𝓝[≠] 0)
      (𝓝 (fun ij : OrbitalPair A => orbitalCoordinate p Z ij.1.1 ij.1.2)) := by
  have h := (continuous_orbitalCoordinates p).continuousAt.tendsto.comp
    (scaledTangentCoordinates_tendsto p hp Z)
  have he : orbitalCoordinates p (tangentDifferential p Z) =
      (fun ij : OrbitalPair A => orbitalCoordinate p Z ij.1.1 ij.1.2) := by
    funext ij
    exact (orbitalCoordinate_differential p Z _ _).symm
  rw [he] at h
  exact h

/-- Exact finite-scale chart identity in the manuscript's coordinates, valid
for every Hermitian tangent in the chart. -/
theorem chart_in_spectral_orbital_coordinates (p : A → ℝ)
    (hgap : ∀ i j, i < j → 0 < p i - p j) (H : Hermitian A) :
    (chart p H : Matrix A A ℂ) + base p =
      NormedSpace.exp (orbitalGenerator p (orbitalCoordinates p H)) *
        Matrix.diagonal (fun i => ((p i + spectralCoordinates H i : ℝ) : ℂ)) *
          NormedSpace.exp (-orbitalGenerator p (orbitalCoordinates p H)) := by
  rw [chart_coe, rawChart, sub_add_cancel, generator_eq_orbitalGenerator p hgap,
    diagonalPart_eq_spectralCoordinates]
  congr 2
  ext a b
  by_cases hab : a = b <;> simp [base, Matrix.diagonal_apply, hab]

end Cloning.PCTLocalChart
