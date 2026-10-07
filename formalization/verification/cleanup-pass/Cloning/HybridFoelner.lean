import Cloning.HybridPrior

/-! Quantitative covariance of actual hybrid probability averages. The error
is uniform over competitors and arbitrary complex L¹ inputs. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k s : ℕ}

lemma weighted_integral_difference_le_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : PhaseSpace k s → E) (hf : Continuous f) (C : ℝ)
    (hn : ∀ ξ, ‖f ξ‖ ≤ C) (p q : PhaseSpace k s → ℝ)
    (hp : Integrable p) (hq : Integrable q) :
    ‖(∫ ξ, p ξ • f ξ) - (∫ ξ, q ξ • f ξ)‖ ≤ C * ∫ ξ, |p ξ - q ξ| := by
  have hi (r : PhaseSpace k s → ℝ) (hr : Integrable r) :
      Integrable (fun ξ => r ξ • f ξ) := by
    apply (hr.norm.mul_const C).mono' (hr.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    exact Eventually.of_forall fun ξ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hn ξ) (norm_nonneg _)
  rw [← integral_sub (hi p hp) (hi q hq)]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ ξ, |p ξ - q ξ| * C := by
      apply integral_mono ((hi p hp).sub (hi q hq)).norm ((hp.sub hq).abs.mul_const C)
      intro ξ
      change ‖p ξ • f ξ - q ξ • f ξ‖ ≤ |p ξ - q ξ| * C
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hn ξ) (abs_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

namespace PhaseDensity
variable (p : PhaseDensity k s)

/-- The actual averaged continuous linear map, with a growing phase-space prior. -/
def foelnerMap (r : ℝ) (Λ : HybridChannel k s) (n : ℕ) :
    HybridSpace k s →L[ℂ] HybridSpace k s := covariantAverageMap (p.expandingPrior n) r Λ

def foelnerChannel (r : ℝ) (Λ : HybridChannel k s) (n : ℕ) : HybridChannel k s :=
  covariantAverage (p.expandingPrior n) r Λ

@[simp] lemma foelnerChannel_map (r : ℝ) (Λ : HybridChannel k s) (n : ℕ) :
    (p.foelnerChannel r Λ n).map = p.foelnerMap r Λ n := rfl

lemma foelnerMap_covariance_bound (r : ℝ) (Λ : HybridChannel k s)
    (b : PhaseSpace k s) (A : HybridSpace k s) (n : ℕ) :
    ‖p.foelnerMap r Λ n (hybridTranslation b A) -
      hybridTranslation (r • b) (p.foelnerMap r Λ n A)‖ ≤ p.covarianceError n b * ‖A‖ := by
  let f : PhaseSpace k s → HybridSpace k s := fun ξ => (translatedChannel r Λ ξ).map A
  have hf : Continuous f := continuous_translatedChannel r Λ A
  change ‖covariantAverageMap (p.expandingPrior n) r Λ (hybridTranslation b A) -
    hybridTranslation (r • b) (covariantAverageMap (p.expandingPrior n) r Λ A)‖ ≤ _
  rw [covariantAverageMap_shift, ← map_sub, norm_hybridTranslation]
  change ‖(∫ ξ, f (ξ + b) ∂p.expandingPrior n) - (∫ ξ, f ξ ∂p.expandingPrior n)‖ ≤ _
  rw [p.integral_expandingPrior_shift n b f hf, p.integral_expandingPrior n f hf]
  have h := weighted_integral_difference_le_bound
    (fun ξ => f (((n : ℝ) + 1) • ξ)) (hf.comp (by fun_prop)) (2 * ‖A‖)
    (fun ξ => (translatedChannel r Λ (((n : ℝ) + 1) • ξ)).norm_le_two A)
    (fun ξ => p.value (-(((n : ℝ) + 1)⁻¹ • b) + ξ)) p.value
    ((measurePreserving_add_left volume (-(((n : ℝ) + 1)⁻¹ • b))).integrable_comp_of_integrable p.integrable)
    p.integrable
  simpa only [covarianceError, translationError, mul_assoc, mul_left_comm, mul_comm] using h

lemma foelnerMap_covariance_tendsto (r : ℝ) (Λ : HybridChannel k s)
    (b : PhaseSpace k s) (A : HybridSpace k s) :
    Tendsto (fun n => ‖p.foelnerMap r Λ n (hybridTranslation b A) -
      hybridTranslation (r • b) (p.foelnerMap r Λ n A)‖) atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _) (p.foelnerMap_covariance_bound r Λ b A)
    (by simpa using (p.covarianceError_tendsto b).mul_const ‖A‖)

/-- Uniformity in the original competitor permits an arbitrary new competitor
at every averaging scale, as required for a supremum inside the limit. -/
lemma foelnerMap_covariance_tendsto_varying (r : ℝ) (Λ : ℕ → HybridChannel k s)
    (b : PhaseSpace k s) (A : HybridSpace k s) :
    Tendsto (fun n => ‖p.foelnerMap r (Λ n) n (hybridTranslation b A) -
      hybridTranslation (r • b) (p.foelnerMap r (Λ n) n A)‖) atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => p.foelnerMap_covariance_bound r (Λ n) b A n)
    (by simpa using (p.covarianceError_tendsto b).mul_const ‖A‖)

lemma foelnerMap_classical_covariance_bound (r : ℝ) (Λ : HybridChannel k s)
    (h : Fin k → ℝ) (A : HybridSpace k s) (n : ℕ) :
    ‖p.foelnerMap r Λ n (classicalTranslation h A) -
      classicalTranslation (r • h) (p.foelnerMap r Λ n A)‖ ≤
        p.covarianceError n (h, 0) * ‖A‖ := by
  simpa only [Prod.smul_mk, smul_zero, hybridTranslation_classical] using
    p.foelnerMap_covariance_bound r Λ (h, 0) A n

lemma foelnerMap_quantum_covariance_tendsto (r : ℝ) (Λ : ℕ → HybridChannel k s)
    (z : Fin s → ℂ) (A : HybridSpace k s) :
    Tendsto (fun n => ‖p.foelnerMap r (Λ n) n (quantumL1Action z A) -
      quantumL1Action (r • z) (p.foelnerMap r (Λ n) n A)‖) atTop (𝓝 0) := by
  simpa only [Prod.smul_mk, smul_zero, hybridTranslation_quantum] using
    p.foelnerMap_covariance_tendsto_varying r Λ (0, z) A

/-- Integrable weighted covariance errors for any integrable reference density. -/
lemma integrable_weighted_classical_error (g : (Fin k → ℝ) → ℝ) (hg : Integrable g) (n : ℕ) :
    Integrable (fun h => g h * p.covarianceError n (h, 0)) := by
  apply (hg.norm.mul_const 4).mono'
    (hg.aestronglyMeasurable.mul
      ((p.continuous_covarianceError n).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  exact Eventually.of_forall fun h => by
    change ‖g h * p.covarianceError n (h, 0)‖ ≤ ‖g h‖ * 4
    rw [norm_mul, Real.norm_of_nonneg (p.covarianceError_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (p.covarianceError_le_four _ _) (norm_nonneg _)

/-- The classical covariance penalty vanishes after Gaussian weighting, with
no uniformity-in-translation premise: a proved bound of four supplies domination. -/
lemma weighted_classical_error_tendsto (g : (Fin k → ℝ) → ℝ) (hg : Integrable g) :
    Tendsto (fun n => ∫ h, g h * p.covarianceError n (h, 0)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun h => ‖g h‖ * 4)
    (fun n => (p.integrable_weighted_classical_error g hg n).aestronglyMeasurable)
    (hg.norm.mul_const 4)
    (fun n => Eventually.of_forall fun h => by
      rw [norm_mul, Real.norm_of_nonneg (p.covarianceError_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (p.covarianceError_le_four _ _) (norm_nonneg _))
    (Eventually.of_forall fun h => by simpa using (p.covarianceError_tendsto (h, 0)).const_mul (g h))
  simpa using h

end PhaseDensity
end Cloning.Hybrid
