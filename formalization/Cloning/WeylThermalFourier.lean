import Cloning.WeylIdlerUniqueness
import Cloning.MultimodeCoherentGaussianMixture
import Mathlib.MeasureTheory.Integral.Prod

/-! The Fourier witness identity for actual coherent mixtures. Normal trace
duality and absolutely integrable scalar Fubini turn the proved Gaussian
vacuum inversion into the thermal operator witness used by the Gaussian
converse. All trace-class test operators, including off-diagonal ones, are
allowed. -/

noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ}

lemma weylCharacter_norm (a b : Fin d → ℂ) : ‖weylCharacter a b‖ = 1 := by
  simp [weylCharacter, norm_div]

lemma continuous_weylCharacter_pair :
    Continuous (fun p : (Fin d → ℂ) × (Fin d → ℂ) => weylCharacter p.1 p.2) := by
  have hp : Continuous (fun p : (Fin d → ℂ) × (Fin d → ℂ) => displacementPhase p.1 p.2) := by
    unfold displacementPhase ComplexCoherent.displacementPhase
    fun_prop
  exact hp.div (hp.comp continuous_swap) (fun p => displacementPhase_ne_zero p.2 p.1)

/-- The diagonal coherent matrix element as an absolutely integrable Weyl
Fourier integral. -/
theorem coherent_diagonal_characteristic_integral
    (T : TraceClass (Fock d)) (z : Fin d → ℂ) :
    ⟪coherentVector z, T.1 (coherentVector z)⟫_ℂ =
      ∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) *
        (weylCharacter z a * tracePairing T (displacement a)) := by
  have h := integral_weighted_characteristic
    (sandwichCLM (displacement (-z)) (displacement z) T)
  rw [tracePairing_sandwich, displaced_vacuum_dyad, tracePairing_rankOne] at h
  rw [← h]
  congr 1
  funext a
  simp only [tracePairing_sandwich, ContinuousLinearMap.mul_def,
    displacement_conjugation, map_smul, smul_eq_mul]

/-- Normal trace pairing commutes with the actual coherent-state Bochner
mixture. -/
theorem tracePairing_coherentMixture (μ : Measure (Fin d → ℂ)) [IsFiniteMeasure μ]
    (T : TraceClass (Fock d)) :
    tracePairing T (∫ z, coherentProjector z ∂μ).1 =
      ∫ z, ⟪coherentVector z, T.1 (coherentVector z)⟫_ℂ ∂μ := by
  have h := ((tracePairing T).comp (inclusionCLM (H := Fock d))).integral_comp_comm
    (integrable_coherentProjector μ)
  simpa only [ContinuousLinearMap.comp_apply, inclusionCLM_apply,
    coherentProjector, vectorProjector, TraceClass.ofOperator_coe,
    tracePairing_rankOne] using h.symm

lemma integrable_coherent_fourier_kernel (μ : Measure (Fin d → ℂ)) [IsFiniteMeasure μ]
    (T : TraceClass (Fock d)) :
    Integrable (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
      (weylGaussianWeight p.2 : ℂ) *
        (weylCharacter p.1 p.2 * tracePairing T (displacement p.2))) (μ.prod volume) := by
  apply ((integrable_weylGaussianWeight.mul_const ‖T‖).comp_snd μ).mono'
  · exact (((Complex.continuous_ofReal.comp continuous_weylGaussianWeight).comp
      continuous_snd).mul (continuous_weylCharacter_pair.mul
        ((continuous_tracePairing_displacement T).comp continuous_snd))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p => by
      rw [norm_mul, norm_mul, weylCharacter_norm, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weylGaussianWeight_nonneg p.2)]
      exact mul_le_mul_of_nonneg_left (norm_tracePairing_displacement_le T p.2)
        (weylGaussianWeight_nonneg p.2))

/-- Exact Fourier witness identity for every finite coherent mixture.
The proof justifies the interchange by a product-integrable bound, uniform in
the coherent amplitude. -/
theorem tracePairing_coherentMixture_fourier
    (μ : Measure (Fin d → ℂ)) [IsFiniteMeasure μ] (T : TraceClass (Fock d)) :
    tracePairing T (∫ z, coherentProjector z ∂μ).1 =
      ∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) *
        ((∫ z, weylCharacter z a ∂μ) * tracePairing T (displacement a)) := by
  rw [tracePairing_coherentMixture]
  simp_rw [coherent_diagonal_characteristic_integral]
  rw [integral_integral_swap (integrable_coherent_fourier_kernel μ T)]
  congr 1
  funext a
  rw [integral_const_mul, integral_mul_const]

end Cloning.MultimodeCoherent
