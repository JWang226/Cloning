import Cloning.PCTGaussianOutputTangent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! The actual joint tangent pushforward is a product measure. Independence
is derived from the joint characteristic of the physical tangent frame. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTJointGaussianLaw
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTGaussianOutput Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {s d : ℕ}

def tangentClassical (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (z : Fin s → ℂ) : A → ℝ := classicalCoordinate p (frameTangentMatrix u z)

lemma continuous_tangentClassical (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ) :
    Continuous (tangentClassical u p) := by
  unfold tangentClassical classicalCoordinate frameTangentMatrix frameTangent
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  fun_prop

def classicalTangentLaw (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ) (v : ℝ) :
    Measure (A → ℝ) := (gaussianProductMeasure (fun _ : Fin s => v)).map (tangentClassical u p)

theorem classicalTangentLaw_probability (u : Fin (s + 1) → Register (A × A))
    (p : A → ℝ) {v : ℝ} (hv : 0 < v) : IsProbabilityMeasure (classicalTangentLaw u p v) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hv)
  unfold classicalTangentLaw
  exact Measure.isProbabilityMeasure_map (continuous_tangentClassical u p).aemeasurable

def orbitalVariance (p : A → ℝ) (e : Fin d ≃ OrbitalPair A) (v : ℝ) (k : Fin d) : ℝ :=
  v * (p (e k).1.1 + p (e k).1.2) / (p (e k).1.1 - p (e k).1.2)

lemma orbitalVariance_pos (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hgap : ∀ i j, i < j → 0 < p i - p j) (e : Fin d ≃ OrbitalPair A)
    {v : ℝ} (hv : 0 < v) (k : Fin d) : 0 < orbitalVariance p e v k :=
  div_pos (mul_pos hv (add_pos (hp _) (hp _))) (hgap _ _ (e k).2)

def jointTangent (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (e : Fin d ≃ OrbitalPair A) (z : Fin s → ℂ) : (A → ℝ) × (Fin d → ℂ) :=
  (tangentClassical u p z, tangentDisplacement u p e z)

lemma continuous_jointTangent (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (e : Fin d ≃ OrbitalPair A) : Continuous (jointTangent u p e) :=
  (continuous_tangentClassical u p).prodMk (continuous_tangentDisplacement u p e)

lemma classical_dual_eq (L : StrongDual ℝ (A → ℝ)) (x : A → ℝ) :
    L x = ∑ a, L (Pi.single a 1) * x a := by
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : A => ℝ) L x]
  apply Finset.sum_congr rfl
  intro a _
  have he : Pi.single a (x a) = (x a) • (Pi.single a (1 : ℝ) : A → ℝ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
  change L (Pi.single a (x a)) = _
  rw [he, map_smul]
  simp [mul_comm]

def orbitalDualTest (L : StrongDual ℝ (Fin d → ℂ)) (k : Fin d) : ℂ :=
  (-(L (Pi.single k Complex.I)) / 2 : ℝ) +
    Complex.I * ((L (Pi.single k 1) / 2 : ℝ) : ℂ)

lemma orbital_dual_phase (L : StrongDual ℝ (Fin d → ℂ)) (z : Fin d → ℂ) :
    Complex.I * (L z : ℂ) = ∑ k,
      (orbitalDualTest L k * star (z k) - star (orbitalDualTest L k) * z k) := by
  have he (k : Fin d) : L (Pi.single k (z k)) =
      (z k).re * L (Pi.single k 1) + (z k).im * L (Pi.single k Complex.I) := by
    have hz : Pi.single k (z k) = (z k).re • (Pi.single k (1 : ℂ) : Fin d → ℂ) +
        (z k).im • (Pi.single k Complex.I : Fin d → ℂ) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      congr 1
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im (z k)).symm
    rw [hz, map_add, map_smul, map_smul]
    rfl
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin d => ℂ) L z]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, he,
    Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Complex.ext <;> simp [orbitalDualTest, Complex.mul_re, Complex.mul_im] <;> ring

lemma weylCharacter_neg_eq_phase (z a : Fin d → ℂ) :
    weylCharacter z (-a) = Complex.exp (∑ k, (a k * star (z k) - star (a k) * z k)) := by
  rw [weylCharacter_eq_prod_exp, ← Complex.exp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.neg_apply, map_neg, starRingEnd_apply]
  ring

lemma orbital_charFunDual {b : Fin d → ℝ} (hb : ∀ k, 0 < b k)
    (L : StrongDual ℝ (Fin d → ℂ)) :
    charFunDual (gaussianProductMeasure b) L =
      ∏ k, Complex.exp (-((b k * ‖orbitalDualTest L k‖ ^ 2 : ℝ) : ℂ)) := by
  rw [charFunDual_apply]
  have he (z : Fin d → ℂ) : Complex.exp ((L z : ℂ) * Complex.I) =
      weylCharacter z (-orbitalDualTest L) := by
    rw [mul_comm, orbital_dual_phase, weylCharacter_neg_eq_phase]
  simp_rw [he]
  rw [integral_weylCharacter_gaussianProductMeasure hb]
  simp

lemma joint_characteristic_reindexed
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (e : Fin d ≃ OrbitalPair A) {v : ℝ} (hv : 0 < v)
    (t : A → ℝ) (a : Fin d → ℂ) :
    (∫ z, Complex.exp (Complex.I * ((∑ i, t i * tangentClassical u p z i : ℝ) : ℂ) +
      ∑ k, (a k * star (tangentDisplacement u p e z k) -
        star (a k) * tangentDisplacement u p e z k))
        ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      Complex.exp (-((v * ((∑ i, p i * (t i) ^ 2) - (∑ i, p i * t i) ^ 2) : ℝ) : ℂ)) *
        ∏ k, Complex.exp (-((orbitalVariance p e v k * ‖a k‖ ^ 2 : ℝ) : ℂ)) := by
  have h := jointCoordinate_characteristic u p hp hu hgap hv t (fun ij => a (e.symm ij))
  have he (z : Fin s → ℂ) :
      (∑ ij : OrbitalPair A, (a (e.symm ij) * star (orbitalCoordinate p
        (frameTangentMatrix u z) ij.1.1 ij.1.2) - star (a (e.symm ij)) *
          orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2)) =
      ∑ k, (a k * star (tangentDisplacement u p e z k) -
        star (a k) * tangentDisplacement u p e z k) := by
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, tangentDisplacement]
  simp_rw [he] at h
  rw [show (∑ ij : OrbitalPair A, v * (p ij.1.1 + p ij.1.2) /
      (p ij.1.1 - p ij.1.2) * ‖a (e.symm ij)‖ ^ 2) =
      ∑ k, orbitalVariance p e v k * ‖a k‖ ^ 2 by
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, orbitalVariance]] at h
  rw [← Complex.exp_sum, ← Complex.exp_add]
  convert h using 1 <;> simp [tangentClassical, Complex.ofReal_add, Complex.ofReal_sum, add_comm]

lemma classical_charFunDual
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    {v : ℝ} (hv : 0 < v) (L : StrongDual ℝ (A → ℝ)) :
    charFunDual (classicalTangentLaw u p v) L =
      Complex.exp (-((v * ((∑ i, p i * (L (Pi.single i 1)) ^ 2) -
        (∑ i, p i * L (Pi.single i 1)) ^ 2) : ℝ) : ℂ)) := by
  rw [charFunDual_apply, classicalTangentLaw,
    integral_map (continuous_tangentClassical u p).aemeasurable (by fun_prop)]
  convert classicalCoordinate_characteristic u p hp hu hv (fun i => L (Pi.single i 1)) using 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [classical_dual_eq, mul_comm _ Complex.I]
  rfl

lemma joint_dual_phase (L : StrongDual ℝ ((A → ℝ) × (Fin d → ℂ)))
    (x : A → ℝ) (z : Fin d → ℂ) :
    (L (x,z) : ℂ) * Complex.I =
      Complex.I * ((∑ i, (L.comp (.inl ℝ (A → ℝ) (Fin d → ℂ))) (Pi.single i 1) * x i : ℝ) : ℂ) +
      ∑ k, (orbitalDualTest (L.comp (.inr ℝ (A → ℝ) (Fin d → ℂ))) k * star (z k) -
        star (orbitalDualTest (L.comp (.inr ℝ (A → ℝ) (Fin d → ℂ))) k) * z k) := by
  rw [← L.comp_inl_add_comp_inr (x,z), Complex.ofReal_add, add_mul]
  rw [classical_dual_eq, mul_comm _ Complex.I, mul_comm _ Complex.I, orbital_dual_phase]

/-- The joint pushforward of the physical tangent coordinates is exactly the
product of its classical marginal and independent circular Gaussian orbital
coordinates. No independence or law-identification premise occurs. -/
theorem jointTangent_map_eq_prod
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (e : Fin d ≃ OrbitalPair A) {v : ℝ} (hv : 0 < v) :
    (gaussianProductMeasure (fun _ : Fin s => v)).map (jointTangent u p e) =
      (classicalTangentLaw u p v).prod (gaussianProductMeasure (orbitalVariance p e v)) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hv)
  letI := gaussianProductMeasure_probability (orbitalVariance_pos p hp hgap e hv)
  letI := classicalTangentLaw_probability u p hv
  apply charFunDual_eq_prod_iff.mp
  intro L
  rw [classical_charFunDual u p (fun a => (hp a).le) hu hv,
    orbital_charFunDual (orbitalVariance_pos p hp hgap e hv), charFunDual_apply,
    integral_map (continuous_jointTangent u p e).aemeasurable (by fun_prop)]
  simp only [jointTangent, joint_dual_phase]
  exact joint_characteristic_reindexed u p (fun a => (hp a).le) hu hgap e hv
    (fun i => (L.comp (.inl ℝ (A → ℝ) (Fin d → ℂ))) (Pi.single i 1))
    (orbitalDualTest (L.comp (.inr ℝ (A → ℝ) (Fin d → ℂ))))

/-- Bochner integration against the tangent frame can be computed against
its now identified product law. -/
theorem integral_jointTangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (e : Fin d ≃ OrbitalPair A) {v : ℝ} (hv : 0 < v)
    (f : (A → ℝ) × (Fin d → ℂ) → E)
    (hf : Integrable f ((classicalTangentLaw u p v).prod
      (gaussianProductMeasure (orbitalVariance p e v)))) :
    (∫ z, f (jointTangent u p e z) ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      ∫ x, ∫ a, f (x,a) ∂gaussianProductMeasure (orbitalVariance p e v)
        ∂classicalTangentLaw u p v := by
  letI := gaussianProductMeasure_probability (orbitalVariance_pos p hp hgap e hv)
  letI := classicalTangentLaw_probability u p hv
  have hm := jointTangent_map_eq_prod u p hp hu hgap e hv
  rw [← integral_prod f hf, ← hm]
  exact (integral_map (continuous_jointTangent u p e).aemeasurable
    (by rw [hm]; exact hf.aestronglyMeasurable)).symm

end Cloning.PCTJointGaussianLaw
