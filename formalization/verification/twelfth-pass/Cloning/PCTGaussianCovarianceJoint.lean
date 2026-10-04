import Cloning.PCTGaussianCovarianceOrbital

/-! The joint characteristic of classical and orbital tangent coordinates.
Every independence factor is obtained from the actual purification frame
Gaussian integral and disjoint computational matrix entries. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTGaussianCovariance
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {s : ℕ}

abbrev OrbitalPair (A : Type*) [LT A] := {ij : A × A // ij.1 < ij.2}

lemma orbitalTest_pairwise (p : A → ℝ) (i j : OrbitalPair A) (hij : i ≠ j) (ξ η : ℂ) :
    ⟪orbitalTest p i.1.1 i.1.2 ξ, orbitalTest p j.1.1 j.1.2 η⟫_ℂ = 0 := by
  have h00 : (i.1.1, i.1.2) ≠ (j.1.1, j.1.2) := by
    intro h
    exact hij (Subtype.ext h)
  have h01 : (i.1.1, i.1.2) ≠ (j.1.2, j.1.1) := by
    intro h
    obtain ⟨h1,h2⟩ := Prod.mk.inj h
    exact (lt_asymm i.2 (by simpa only [h1,h2] using j.2))
  have h10 : (i.1.2, i.1.1) ≠ (j.1.1, j.1.2) := by
    intro h
    apply h01
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have h11 : (i.1.2, i.1.1) ≠ (j.1.2, j.1.1) := by
    intro h
    apply h00
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  simp only [orbitalTest, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    (registerBasis (A × A)).orthonormal.inner_eq_zero h00,
    (registerBasis (A × A)).orthonormal.inner_eq_zero h01,
    (registerBasis (A × A)).orthonormal.inner_eq_zero h10,
    (registerBasis (A × A)).orthonormal.inner_eq_zero h11, mul_zero, add_zero]

lemma classicalTest_orthogonal_orbitalTest (p t : A → ℝ) (i j : A) (hij : i ≠ j) (ξ : ℂ) :
    ⟪coefficientVector (classicalTest p t), orbitalTest p i j ξ⟫_ℂ = 0 := by
  have hi (a b : A) (hab : a ≠ b) :
      ⟪coefficientVector (classicalTest p t), lp.single 2 (a,b) 1⟫_ℂ = 0 := by
    rw [← inner_conj_symm]
    simp [register_inner_single, coefficientVector_apply, classicalTest, hab]
  simp only [orbitalTest, inner_add_right, inner_smul_right, registerBasis_apply,
    hi i j hij, hi j i hij.symm, mul_zero, add_zero]

lemma norm_sum_sq_of_pairwise {K : Type*} [Fintype K] [DecidableEq K]
    (f : K → Register (A × A)) (h : Pairwise (fun i j => ⟪f i, f j⟫_ℂ = 0)) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  have he : ⟪∑ i, f i, ∑ i, f i⟫_ℂ = ∑ i, ⟪f i, f i⟫_ℂ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact h hji
    · simp
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
    using congrArg Complex.re he

/-- Test vector for all classical and orbital variables together. -/
def jointTest (p t : A → ℝ) (ξ : OrbitalPair A → ℂ) : Register (A × A) :=
  coefficientVector (classicalTest p t) +
    ∑ ij, orbitalTest p ij.1.1 ij.1.2 (ξ ij)

lemma jointTest_phase (p t : A → ℝ) (ξ : OrbitalPair A → ℂ) (Z : Matrix A A ℂ) :
    ⟪jointTest p t ξ, coefficientVector Z⟫_ℂ -
      ⟪coefficientVector Z, jointTest p t ξ⟫_ℂ =
        Complex.I * ((∑ a, t a * classicalCoordinate p Z a : ℝ) : ℂ) +
          ∑ ij, (ξ ij * star (orbitalCoordinate p Z ij.1.1 ij.1.2) -
            star (ξ ij) * orbitalCoordinate p Z ij.1.1 ij.1.2) := by
  simp only [jointTest, inner_add_left, inner_add_right, sum_inner, inner_sum]
  rw [show (⟪coefficientVector (classicalTest p t), coefficientVector Z⟫_ℂ +
      ∑ ij : OrbitalPair A, ⟪orbitalTest p ij.1.1 ij.1.2 (ξ ij), coefficientVector Z⟫_ℂ) -
      (⟪coefficientVector Z, coefficientVector (classicalTest p t)⟫_ℂ +
      ∑ ij : OrbitalPair A, ⟪coefficientVector Z, orbitalTest p ij.1.1 ij.1.2 (ξ ij)⟫_ℂ) =
    (⟪coefficientVector (classicalTest p t), coefficientVector Z⟫_ℂ -
      ⟪coefficientVector Z, coefficientVector (classicalTest p t)⟫_ℂ) +
      ∑ ij : OrbitalPair A, (⟪orbitalTest p ij.1.1 ij.1.2 (ξ ij), coefficientVector Z⟫_ℂ -
        ⟪coefficientVector Z, orbitalTest p ij.1.1 ij.1.2 (ξ ij)⟫_ℂ) by
          rw [Finset.sum_sub_distrib]; ring]
  simp only [classicalTest_phase, orbitalTest_phase]

lemma jointTest_norm_sq (p t : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hgap : ∀ i j, i < j → 0 < p i - p j) (ξ : OrbitalPair A → ℂ) :
    ‖jointTest p t ξ‖ ^ 2 = (∑ a, p a * (t a) ^ 2) +
      ∑ ij, (p ij.1.1 + p ij.1.2) / (p ij.1.1 - p ij.1.2) * ‖ξ ij‖ ^ 2 := by
  have ho : ⟪coefficientVector (classicalTest p t),
      ∑ ij : OrbitalPair A, orbitalTest p ij.1.1 ij.1.2 (ξ ij)⟫_ℂ = 0 := by
    simp only [inner_sum]
    apply Finset.sum_eq_zero
    intro ij _
    exact classicalTest_orthogonal_orbitalTest p t _ _ (ne_of_lt ij.2) _
  rw [jointTest, norm_add_sq (𝕜 := ℂ), ho, map_zero, mul_zero, add_zero,
    classicalTest_norm_sq p t hp,
    norm_sum_sq_of_pairwise _ (fun i j hij => orbitalTest_pairwise p i j hij _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  exact orbitalTest_norm_sq p _ _ (ne_of_lt ij.2) (hp _) (hp _) (hgap _ _ ij.2) _

lemma jointTest_reference_sq (p t : A → ℝ) (hp : ∀ a, 0 ≤ p a) (ξ : OrbitalPair A → ℂ) :
    ‖⟪coefficientVector (schmidtCoefficients p), jointTest p t ξ⟫_ℂ‖ ^ 2 =
      (∑ a, p a * t a) ^ 2 := by
  have ho : (∑ ij : OrbitalPair A, ⟪coefficientVector (schmidtCoefficients p),
      orbitalTest p ij.1.1 ij.1.2 (ξ ij)⟫_ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro ij _
    exact orbitalTest_orthogonal_reference p _ _ (ne_of_lt ij.2) _
  simp only [jointTest, inner_add_right, inner_sum, ho, add_zero,
    classicalTest_reference_sq p t hp]

/-- The full joint characteristic, with exact classical covariance `2 v Σp`
and independent circular orbital variances `v (pᵢ+pⱼ)/(pᵢ-pⱼ)`. The additive
exponent is derived from the integral, with no independence hypothesis. -/
theorem jointCoordinate_characteristic
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    {v : ℝ} (hv : 0 < v) (t : A → ℝ) (ξ : OrbitalPair A → ℂ) :
    (∫ z, Complex.exp (Complex.I * ((∑ a,
      t a * classicalCoordinate p (frameTangentMatrix u z) a : ℝ) : ℂ) +
        ∑ ij, (ξ ij * star (orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2) -
          star (ξ ij) * orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2))
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * ((∑ a, p a * (t a) ^ 2) - (∑ a, p a * t a) ^ 2) +
        ∑ ij, v * (p ij.1.1 + p ij.1.2) / (p ij.1.1 - p ij.1.2) * ‖ξ ij‖ ^ 2 : ℝ) : ℂ)) := by
  simp_rw [← jointTest_phase, coefficientVector_frameTangentMatrix]
  rw [frameTangent_characteristic u hv, hu, jointTest_norm_sq p t hp hgap,
    jointTest_reference_sq p t hp]
  congr 1
  norm_cast
  simp_rw [div_eq_mul_inv, mul_sub, mul_add, Finset.mul_sum, mul_assoc]
  ring

end Cloning.PCTGaussianCovariance
