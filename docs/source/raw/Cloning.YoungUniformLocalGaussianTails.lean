import Cloning.YoungUniformLocalGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Uniform integrable domination and Gaussian tails on the actual Euclidean
root hyperplane, derived from a uniform positive spectral lower bound. -/

noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def gaussianEnvelope (d : ℕ) (a : ℝ) (x : rootSpace d) : ℝ :=
  Real.exp (-(d : ℝ) / 2 * Real.log (2 * Real.pi) - 1 / 2 * Real.log ((d : ℝ) + 1) -
    1 / 2 * ((d : ℝ) + 1) * Real.log a) * Real.exp (-‖x‖ ^ 2 / 2)

theorem integrable_gaussianEnvelope (d : ℕ) (a : ℝ) :
    Integrable (gaussianEnvelope d a) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := rootSpace d) (b := (1 / 2 : ℂ)) (by norm_num) 0 (0 : rootSpace d)
  have hh : Integrable (fun x : rootSpace d ↦ Real.exp (-‖x‖ ^ 2 / 2)) volume := by
    convert h.norm using 1
    ext x
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
    <;> ring
  exact hh.const_mul _

/-- A single integrable envelope dominates all normalized spectra bounded
below by `a`; neither spectral eigenvectors nor a density tail is a premise. -/
theorem covarianceGaussian_le_envelope (d : ℕ) (a : ℝ) (ha : 0 < a)
    (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1) (hpa : ∀ i, a ≤ p i)
    (x : rootSpace d) :
    covarianceGaussian d p hp x ≤ gaussianEnvelope d a x := by
  have hp0 i : 0 < p i := ha.trans_le (hpa i)
  have hp1 i : p i ≤ 1 := by
    rw [← hp]
    exact Finset.single_le_sum (fun j _ ↦ (hp0 j).le) (Finset.mem_univ i)
  have hl : ((d : ℝ) + 1) * Real.log a ≤ ∑ i, Real.log (p i) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ Real.log_le_log ha (hpa i))
    simpa using h
  have hquad : ‖x‖ ^ 2 ≤ ∑ i, (x.1 i) ^ 2 / p i := by
    change ‖x.1‖ ^ 2 ≤ _
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
    exact (le_div_iff₀ (hp0 i)).mpr (mul_le_of_le_one_right (sq_nonneg _) (hp1 i))
  rw [covarianceGaussian_eq_exp d p hp hp0 x, gaussianEnvelope, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem gaussianEnvelope_tail_tendsto_zero (d : ℕ) (a : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ x in (Metric.closedBall (0 : rootSpace d) (n : ℝ))ᶜ,
      gaussianEnvelope d a x ∂volume) atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_of_antitone
    (fun n : ℕ ↦ (Metric.isClosed_closedBall (x := (0 : rootSpace d)) (ε := (n : ℝ))).measurableSet.compl)
    (show Antitone (fun n : ℕ ↦ (Metric.closedBall (0 : rootSpace d) (n : ℝ))ᶜ) by
      intro m n hmn
      exact Set.compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)))
    ⟨0, (integrable_gaussianEnvelope d a).integrableOn⟩
  have hempty : (⋂ n : ℕ, (Metric.closedBall (0 : rootSpace d) (n : ℝ))ᶜ) = ∅ := by
    rw [← Set.compl_iUnion, Metric.iUnion_closedBall_nat, Set.compl_univ]
  simpa only [hempty, setIntegral_empty] using ht

/-- Uniform Gaussian tightness, with the common radius constructed from the
explicit integrable envelope. -/
theorem covarianceGaussian_uniform_tails (d : ℕ) (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (p : Fin (d + 1) → ℝ) (hp : ∑ i, p i = 1),
      (∀ i, a ≤ p i) →
      (∫ x in (Metric.closedBall (0 : rootSpace d) (R : ℝ))ᶜ,
        covarianceGaussian d p hp x ∂volume) < ε := by
  obtain ⟨R, hR⟩ := ((gaussianEnvelope_tail_tendsto_zero d a).eventually (gt_mem_nhds hε)).exists
  refine ⟨R, ?_⟩
  intro p hp hpa
  apply lt_of_le_of_lt ?_ hR
  exact integral_mono (integrable_covarianceGaussian d p hp (fun i ↦ ha.trans_le (hpa i))).integrableOn
    (integrable_gaussianEnvelope d a).integrableOn (covarianceGaussian_le_envelope d a ha p hp hpa)

end Cloning.YoungHyperplane
