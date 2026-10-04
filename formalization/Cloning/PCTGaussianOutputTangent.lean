import Cloning.PCTGaussianCovarianceJoint

/-! Actual tangent displacement averaging gives the product PCT thermal
output. This identifies the Gaussian comparison operator directly from the
frame tangent integral, without assuming a pushforward law or independence. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTGaussianOutput
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {s d : ℕ}

def tangentDisplacement (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (e : Fin d ≃ OrbitalPair A) (z : Fin s → ℂ) : Fin d → ℂ :=
  fun k => orbitalCoordinate p (frameTangentMatrix u z) (e k).1.1 (e k).1.2

lemma continuous_tangentDisplacement (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ)
    (e : Fin d ≃ OrbitalPair A) : Continuous (tangentDisplacement u p e) := by
  unfold tangentDisplacement orbitalCoordinate frameTangentMatrix frameTangent
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  fun_prop

lemma tangentDisplacement_characteristic
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (e : Fin d ≃ OrbitalPair A) {v : ℝ} (hv : 0 < v) (a : Fin d → ℂ) :
    (∫ z, weylCharacter (tangentDisplacement u p e z) (-a)
      ∂gaussianProductMeasure (fun _ : Fin s => v)) =
      ∏ k, Complex.exp (-((v * (p (e k).1.1 + p (e k).1.2) /
        (p (e k).1.1 - p (e k).1.2) * ‖a k‖ ^ 2 : ℝ) : ℂ)) := by
  have h := jointCoordinate_characteristic u p hp hu hgap hv (fun _ => 0)
    (fun ij => a (e.symm ij))
  simp only [zero_mul, Finset.sum_const_zero, zero_pow (by omega : 2 ≠ 0), sub_zero,
    Complex.ofReal_zero, mul_zero, zero_add] at h
  have he (z : Fin s → ℂ) : weylCharacter (tangentDisplacement u p e z) (-a) =
      Complex.exp (∑ ij : OrbitalPair A,
        (a (e.symm ij) * star (orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2) -
          star (a (e.symm ij)) * orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2)) := by
    rw [weylCharacter_eq_prod_exp, ← Complex.exp_sum,
      ← e.sum_comp (fun ij : OrbitalPair A =>
        a (e.symm ij) * star (orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2) -
          star (a (e.symm ij)) * orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [tangentDisplacement, Equiv.symm_apply_apply, Pi.neg_apply, map_neg,
      starRingEnd_apply]
    ring
  simp_rw [he]
  rw [h, ← Complex.exp_sum]
  congr 1
  rw [← e.sum_comp (fun ij : OrbitalPair A =>
    v * (p ij.1.1 + p ij.1.2) / (p ij.1.1 - p ij.1.2) * ‖a (e.symm ij)‖ ^ 2)]
  simp only [Equiv.symm_apply_apply, Complex.ofReal_sum, Finset.sum_neg_distrib]

lemma integrable_tangent_displacement
    (u : Fin (s + 1) → Register (A × A)) (p : A → ℝ) (e : Fin d ≃ OrbitalPair A)
    (μ : Measure (Fin s → ℂ)) [IsFiniteMeasure μ] (T : TraceClass (Fock d)) :
    Integrable (fun z => displacementTraceMap (tangentDisplacement u p e z) T) μ := by
  apply (integrable_const ‖T‖).mono'
    ((continuous_displacementTraceMap T).comp (continuous_tangentDisplacement u p e)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => (displacementTraceMap_norm _ T).le)

/-- The actual quantum Gaussian comparison output obtained from the
purification tangent, with all orbital modes coupled through the same frame.
The joint characteristic proves that the output factors as PCT thermals. -/
theorem tangent_displacement_productThermal_pct
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (e : Fin d ≃ OrbitalPair A) (g : ℝ) (hg : 1 < g) :
    let q : Fin d → ℝ := fun k => p (e k).1.2 / p (e k).1.1
    (∫ z, displacementTraceMap (tangentDisplacement u p e z)
      (vectorMixture (numberBasis d) (productGeometric q))
      ∂gaussianProductMeasure (fun _ : Fin s => g - 1)) =
        vectorMixture (numberBasis d) (productGeometric (fun k => Thermal.pct g (q k))) := by
  dsimp only
  let q : Fin d → ℝ := fun k => p (e k).1.2 / p (e k).1.1
  have hq0 (k : Fin d) : 0 < q k := div_pos (hp _) (hp _)
  have hq1 (k : Fin d) : q k < 1 := by
    exact (div_lt_one (hp _)).mpr (by linarith [hgap _ _ (e k).2])
  have hb (k : Fin d) : 0 < pctDisplacementVariance g (q k) :=
    pctDisplacementVariance_pos hg (hq0 k).le (hq1 k)
  rw [← gaussian_displacement_productThermal_pct g hg hq0 hq1]
  apply characteristic_injective
  funext a
  dsimp only
  letI := gaussianProductMeasure_probability (fun _ : Fin s => sub_pos.mpr hg)
  have h := (tracePairingCLM.flip (displacement a)).integral_comp_comm
    (integrable_tangent_displacement u p e
      (gaussianProductMeasure (fun _ : Fin s => g - 1))
      (vectorMixture (numberBasis d) (productGeometric q)))
  change (∫ z, tracePairing (displacementTraceMap (tangentDisplacement u p e z)
    (vectorMixture (numberBasis d) (productGeometric q))) (displacement a)
      ∂gaussianProductMeasure (fun _ : Fin s => g - 1)) =
    tracePairing (∫ z, displacementTraceMap (tangentDisplacement u p e z)
      (vectorMixture (numberBasis d) (productGeometric q))
      ∂gaussianProductMeasure (fun _ : Fin s => g - 1)) (displacement a) at h
  rw [← h]
  simp_rw [displacement_characteristic]
  rw [integral_mul_const, tangentDisplacement_characteristic u p (fun i => (hp i).le)
    hu hgap e (sub_pos.mpr hg), gaussian_displacement_characteristic hb]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [orbitalVariance_eq_pctDisplacementVariance g _ _ (hp _) (by linarith [hgap _ _ (e k).2])]

end Cloning.PCTGaussianOutput
