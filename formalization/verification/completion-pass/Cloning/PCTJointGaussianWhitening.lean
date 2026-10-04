import Cloning.PCTGaussianCovarianceClassical
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! An explicit whitening chart for the classical purification differential.
The real frame is constructed through the normalized square-root spectrum;
no Gaussian-law or independence assumption is involved. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.PCTJointGaussianWhitening
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] {k s : ℕ}

def sqrtSpectrum (p : A → ℝ) : EuclideanSpace ℝ A := WithLp.toLp 2 (fun a => Real.sqrt (p a))

theorem sqrtSpectrum_norm (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    ‖sqrtSpectrum p‖ = 1 := by
  have h : ‖sqrtSpectrum p‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [sqrtSpectrum, WithLp.ofLp_toLp, Real.sq_sqrt (hp _)] using hs
  nlinarith [norm_nonneg (sqrtSpectrum p)]

theorem exists_whitening_frame (hcard : Fintype.card A = k + 1)
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    ∃ b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A), b 0 = sqrtSpectrum p := by
  classical
  have hc : Module.finrank ℝ (EuclideanSpace ℝ A) = Fintype.card (Fin (k+1)) := by
    simpa using hcard
  let v : Fin (k + 1) → EuclideanSpace ℝ A := fun _ => sqrtSpectrum p
  have hv : Orthonormal ℝ (({0} : Set (Fin (k + 1))).restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp only [hi, ite_true, Set.restrict_apply, v, real_inner_self_eq_norm_sq,
      sqrtSpectrum_norm p hp hs, one_pow]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hc
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

def whiten (p : A → ℝ) (b : Fin (k + 1) → EuclideanSpace ℝ A) (h : A → ℝ) : Fin k → ℝ :=
  fun i => ∑ a, b i.succ a * h a / Real.sqrt (p a)

theorem continuous_whiten (p : A → ℝ) (b : Fin (k + 1) → EuclideanSpace ℝ A) :
    Continuous (whiten p b) := by
  unfold whiten
  fun_prop

def whiteningVector (b : Fin (k + 1) → EuclideanSpace ℝ A) (t : Fin k → ℝ) :
    EuclideanSpace ℝ A := ∑ i, t i • b i.succ

def whiteningTest (p : A → ℝ) (b : Fin (k + 1) → EuclideanSpace ℝ A) (t : Fin k → ℝ) : A → ℝ :=
  fun a => whiteningVector b t a / Real.sqrt (p a)

theorem whiten_dual (p : A → ℝ) (b : Fin (k + 1) → EuclideanSpace ℝ A)
    (t : Fin k → ℝ) (h : A → ℝ) :
    ∑ i, t i * whiten p b h i = ∑ a, whiteningTest p b t a * h a := by
  simp only [whiten, whiteningTest, whiteningVector, Finset.mul_sum,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem whiteningVector_orthogonal
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A)) (t : Fin k → ℝ) :
    ⟪b 0, whiteningVector b t⟫_ℝ = 0 := by
  simp only [whiteningVector, inner_sum, inner_smul_right]
  apply Finset.sum_eq_zero
  intro i _
  rw [b.orthonormal.inner_eq_zero (Fin.succ_ne_zero i).symm]
  simp

theorem whiteningVector_norm_sq
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A)) (t : Fin k → ℝ) :
    ‖whiteningVector b t‖ ^ 2 = ∑ i, (t i) ^ 2 := by
  have h := (b.orthonormal.comp _ (Fin.succ_injective _)).inner_sum t t Finset.univ
  simpa [whiteningVector, real_inner_self_eq_norm_sq, Function.comp_def, pow_two] using h

theorem whiteningTest_reference (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (t : Fin k → ℝ) :
    ∑ a, p a * whiteningTest p b t a = 0 := by
  have h := whiteningVector_orthogonal b t
  rw [hb, EuclideanSpace.inner_eq_star_dotProduct] at h
  have h' : (∑ a, Real.sqrt (p a) * whiteningVector b t a) = 0 := by
    simpa [dotProduct, sqrtSpectrum, mul_comm] using h
  rw [← h']
  apply Finset.sum_congr rfl
  intro a _
  unfold whiteningTest
  have hs := Real.sq_sqrt (hp a).le
  have hn := (Real.sqrt_pos.mpr (hp a)).ne'
  field_simp [hn]
  rw [hs]
  ring

theorem whiteningTest_quadratic (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) (t : Fin k → ℝ) :
    (∑ a, p a * (whiteningTest p b t a) ^ 2) -
      (∑ a, p a * whiteningTest p b t a) ^ 2 = ∑ i, (t i) ^ 2 := by
  rw [whiteningTest_reference p hp b hb, zero_pow (by omega : 2 ≠ 0), sub_zero,
    ← whiteningVector_norm_sq b t, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro a _
  unfold whiteningTest
  rw [div_pow, Real.sq_sqrt (hp a).le]
  field_simp [(hp a).ne']

/-- Whitening the actual score yields covariance `2v I`, with the factor two
fixed by the characteristic exponent. -/
theorem whitenedClassical_characteristic
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ A))
    (hb : b 0 = sqrtSpectrum p) {v : ℝ} (hv : 0 < v) (t : Fin k → ℝ) :
    (∫ z, Complex.exp (Complex.I * ((∑ i, t i *
      whiten p b (classicalCoordinate p (frameTangentMatrix u z)) i : ℝ) : ℂ))
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * (∑ i, (t i) ^ 2) : ℝ) : ℂ)) := by
  simp_rw [whiten_dual]
  rw [classicalCoordinate_characteristic u p (fun a => (hp a).le) hu hv,
    whiteningTest_quadratic p hp b hb]

end Cloning.PCTJointGaussianWhitening
