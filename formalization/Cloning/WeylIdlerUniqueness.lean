import Cloning.HeisenbergDualContinuity

/-! Weyl characteristic functions determine actual trace-class operators.
The proof uses the proved Gaussian strong integral of Weyl operators and the
proved density of coherent vectors; no operator-algebra density or uniqueness
theorem is assumed. Consequently any reconstructed idler is unique. -/

noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d : ℕ}

lemma norm_tracePairing_displacement_le (T : TraceClass (Fock d)) (a : Fin d → ℂ) :
    ‖tracePairing T (displacement a)‖ ≤ ‖T‖ := by
  have hT : ‖tracePairing T‖ ≤ ‖T‖ :=
    ((tracePairingCLM (H := Fock d)).le_opNorm T).trans (by
      simpa using mul_le_mul_of_nonneg_right
        (norm_tracePairingCLM_le (H := Fock d)) (norm_nonneg T))
  calc
    _ ≤ ‖tracePairing T‖ * ‖displacement a‖ := (tracePairing T).le_opNorm _
    _ ≤ ‖T‖ * 1 := mul_le_mul hT (displacement_opNorm_le a) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

lemma integrable_weighted_characteristic (T : TraceClass (Fock d)) :
    Integrable (fun a : Fin d → ℂ =>
      (weylGaussianWeight a : ℂ) * tracePairing T (displacement a)) := by
  apply (integrable_weylGaussianWeight.mul_const ‖T‖).mono'
    (((Complex.continuous_ofReal.comp continuous_weylGaussianWeight).mul
      (continuous_tracePairing_displacement T)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun a => by
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weylGaussianWeight_nonneg a)]
    exact mul_le_mul_of_nonneg_left (norm_tracePairing_displacement_le T a)
      (weylGaussianWeight_nonneg a))

lemma norm_integral_weighted_characteristic_le (T : TraceClass (Fock d)) :
    ‖∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) * tracePairing T (displacement a)‖ ≤
      2 ^ d * ‖T‖ := by
  calc
    _ ≤ ∫ a : Fin d → ℂ,
        ‖(weylGaussianWeight a : ℂ) * tracePairing T (displacement a)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ a : Fin d → ℂ, weylGaussianWeight a * ‖T‖ := by
      apply integral_mono (integrable_weighted_characteristic T).norm
        (integrable_weylGaussianWeight.mul_const ‖T‖)
      intro a
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weylGaussianWeight_nonneg a)]
      exact mul_le_mul_of_nonneg_left (norm_tracePairing_displacement_le T a)
        (weylGaussianWeight_nonneg a)
    _ = _ := by rw [integral_mul_const, integral_weylGaussianWeight]

/-- Gaussian integration of the characteristic function is bounded for the
actual trace norm, allowing extension from finite-rank tests. -/
def gaussianCharacteristicIntegral : TraceClass (Fock d) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T => ∫ a : Fin d → ℂ,
        (weylGaussianWeight a : ℂ) * tracePairing T (displacement a)
      map_add' := by
        intro S T
        simp only [← tracePairingCLM_apply, map_add, ContinuousLinearMap.add_apply, mul_add]
        exact integral_add (integrable_weighted_characteristic S)
          (integrable_weighted_characteristic T)
      map_smul' := by
        intro c T
        simp only [← tracePairingCLM_apply, map_smul, ContinuousLinearMap.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm (weylGaussianWeight _ : ℂ) c]
        exact integral_const_mul _ _ }
    (2 ^ d) norm_integral_weighted_characteristic_le

/-- The Gaussian reconstruction identity for every trace-class operator,
including complex off-diagonal inputs. -/
theorem integral_weighted_characteristic (T : TraceClass (Fock d)) :
    (∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) * tracePairing T (displacement a)) =
      tracePairing T (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) := by
  have heq : gaussianCharacteristicIntegral (d := d) =
      (tracePairingCLM (H := Fock d)).flip
        (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) := by
    apply traceClass_functional_ext
    intro x
    rw [show vectorProjector x = rankOneOperator x x from rfl]
    change (∫ a : Fin d → ℂ,
      (weylGaussianWeight a : ℂ) * tracePairing (rankOneOperator x x) (displacement a)) =
      tracePairing (rankOneOperator x x)
        (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0))
    simp only [tracePairing_rankOneOperator]
    rw [← weylGaussianAverage_eq_vacuumProjector, weylGaussianAverage_apply]
    have h := (innerSL ℂ x).integral_comp_comm (integrable_weighted_displacement x)
    simpa only [innerSL_apply_apply, inner_smul_right] using h
  exact congrArg (fun L : TraceClass (Fock d) →L[ℂ] ℂ => L T) heq

/-- Left and right displacement of the vacuum projector gives every coherent
dyad, with no phase because displacement of the vacuum has unit phase. -/
theorem displaced_vacuum_dyad (a b : Fin d → ℂ) :
    displacement a * (InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0)) *
      displacement (-b) = InnerProductSpace.rankOne ℂ (coherentVector a) (coherentVector b) := by
  apply ContinuousLinearMap.ext
  intro x
  change displacement a (⟪coherentVector 0, displacement (-b) x⟫_ℂ • coherentVector 0) =
    ⟪coherentVector b, x⟫_ℂ • coherentVector a
  rw [map_smul, displacement_vacuum]
  congr 1
  rw [← displacement_adjoint b, ContinuousLinearMap.adjoint_inner_right, displacement_vacuum]

/-- Gaussian Weyl inversion recovers every coherent matrix element of an
arbitrary complex trace-class operator, with the exact displacement phases. -/
theorem characteristic_reconstruction_coherent_matrix_element
    (T : TraceClass (Fock d)) (a b : Fin d → ℂ) :
    ⟪coherentVector b, T.1 (coherentVector a)⟫_ℂ =
      ∫ z : Fin d → ℂ, (weylGaussianWeight z : ℂ) *
        (displacementPhase a z * displacementPhase (a + z) (-b) *
          tracePairing T (displacement (a + z - b))) := by
  have h := integral_weighted_characteristic
    (sandwichCLM (displacement (-b)) (displacement a) T)
  rw [tracePairing_sandwich, displaced_vacuum_dyad, tracePairing_rankOne] at h
  rw [← h]
  congr 1
  funext z
  simp only [tracePairing_sandwich, ContinuousLinearMap.mul_def, displacement_comp,
    ContinuousLinearMap.smul_comp, smul_smul, map_smul, smul_eq_mul, sub_eq_add_neg]

/-- Vanishing Weyl characteristic function forces an actual trace-class
operator to vanish. -/
theorem traceClass_eq_zero_of_characteristic_zero (T : TraceClass (Fock d))
    (hT : ∀ a : Fin d → ℂ, tracePairing T (displacement a) = 0) : T = 0 := by
  have hcoeff (a b : Fin d → ℂ) : ⟪coherentVector b, T.1 (coherentVector a)⟫_ℂ = 0 := by
    let S := sandwichCLM (displacement (-b)) (displacement a) T
    have hS (z : Fin d → ℂ) : tracePairing S (displacement z) = 0 := by
      rw [show S = sandwichCLM (displacement (-b)) (displacement a) T from rfl,
        tracePairing_sandwich]
      simp only [ContinuousLinearMap.mul_def, displacement_comp,
        ContinuousLinearMap.smul_comp, smul_smul, map_smul, hT, smul_zero]
    have h := integral_weighted_characteristic S
    simp only [hS, mul_zero, integral_zero] at h
    rw [show S = sandwichCLM (displacement (-b)) (displacement a) T from rfl,
      tracePairing_sandwich, displaced_vacuum_dyad, tracePairing_rankOne] at h
    exact h.symm
  apply Subtype.ext
  apply continuousLinearMap_ext_coherent
  intro a
  change T.1 (coherentVector a) = 0
  exact coherentVector_total _ (hcoeff a)

/-- The actual Weyl characteristic function is injective on the entire
complex trace class, so it distinguishes arbitrary mixed states. -/
theorem characteristic_injective :
    Function.Injective (fun T : TraceClass (Fock d) => fun a => tracePairing T (displacement a)) := by
  intro S T h
  apply sub_eq_zero.mp
  apply traceClass_eq_zero_of_characteristic_zero
  intro a
  change ((tracePairingCLM (H := Fock d)).flip (displacement a)) (S - T) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h a)

/-- Uniqueness also holds after the nonzero rescaling and phase conjugation
used by an amplifier idler characteristic function. -/
theorem idler_characteristic_injective (s : ℝ) (hs : s ≠ 0) :
    Function.Injective (fun T : TraceClass (Fock d) =>
      fun a : Fin d → ℂ => tracePairing T (displacement (s • star a))) := by
  intro S T h
  apply characteristic_injective
  funext a
  have ha := congrFun h ((s⁻¹) • star a)
  have heq : s • star ((s⁻¹) • star a) = a := by
    simp only [star_smul, star_inv, star_trivial, star_star, smul_smul,
      mul_inv_cancel₀ hs, one_smul]
  simpa only [heq] using ha

end Cloning.MultimodeCoherent
