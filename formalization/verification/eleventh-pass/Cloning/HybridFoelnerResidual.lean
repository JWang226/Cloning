import Cloning.HybridClassicalAverageBound
import Cloning.UniversalGaussianConverse
import Cloning.InfiniteTraceClassAsymptoticBound

/-! Compact quantum residuals of actual approximately covariant hybrid maps.
The Gaussian classical trace factor is derived from translations before
passing to the compact-observable limit; escaping trace is retained. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k s : ℕ}

/-- Weighted quantum covariance follows from the actual hybrid covariance
defect on each fixed input, without an operator-norm covariance premise. -/
lemma weightedQuantumMap_weyl_defect_tendsto
    (Λ : ℕ → Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) →ₗ[ℂ]
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)))
    (r : ℝ) (G : (Fin k → ℝ) → ℝ) (hG : Integrable G)
    (χ : (Fin k → ℝ) → ℝ) (hχ : AEStronglyMeasurable χ volume)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (hquantum : ∀ z R, Tendsto (fun n =>
      ‖Λ n (quantumL1Action z R) - quantumL1Action (r • z) (Λ n R)‖) atTop (𝓝 0))
    (z : Fin s → ℂ) (X : TraceClass (Fock s)) :
    Tendsto (fun n => ‖weightedQuantumMap (Λ n) G hG χ hχ hbound
      (displacementTraceMap z X) - displacementTraceMap (r • z)
        (weightedQuantumMap (Λ n) G hG χ hχ hbound X)‖) atTop (𝓝 0) := by
  have hb (n : ℕ) : ‖weightedQuantumMap (Λ n) G hG χ hχ hbound
      (displacementTraceMap z X) - displacementTraceMap (r • z)
        (weightedQuantumMap (Λ n) G hG χ hχ hbound X)‖ ≤
      C * ‖Λ n (quantumL1Action z (prepareL1 G hG X)) -
        quantumL1Action (r • z) (Λ n (prepareL1 G hG X))‖ := by
    change ‖weightedL1Integral χ hχ hbound
        (Λ n (prepareL1 G hG (displacementTraceMap z X))) -
      displacementTraceMap (r • z) (weightedL1Integral χ hχ hbound
        (Λ n (prepareL1 G hG X)))‖ ≤ _
    rw [prepareL1_compLp, ← weightedL1Integral_compLp, ← map_sub]
    exact norm_weightedL1Integral_le χ hχ hbound _
  exact squeeze_zero (fun _ => norm_nonneg _) hb
    (by simpa using (hquantum z (prepareL1 G hG X)).const_mul C)

/-- One subsequence of the actual weighted hybrid maps converges against
every compact quantum observable to a CP covariant residual with the sharp
classical Gaussian trace bound. -/
theorem exists_gaussian_weighted_covariant_residual
    (Λ : ℕ → Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ]
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)))
    (hΛ : ∀ n, L1CompletelyPositive (Λ n).toLinearMap)
    (hTP : ∀ n, L1TracePreserving (Λ n).toLinearMap)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) {g : ℝ} (hg : 1 ≤ g)
    (hχ : AEStronglyMeasurable
      (GaussianAffinity.productWitness a (fun i => a i / g)) volume)
    {C : ℝ} (hC : 0 ≤ C) (hχbound : ∀ y,
      ‖GaussianAffinity.productWitness a (fun i => a i / g) y‖ ≤ C)
    (b : ℕ → (Fin k → ℝ) → ℝ)
    (hb : ∀ n, AEStronglyMeasurable (b n) volume)
    {B : ℝ} (hbbound : ∀ n h, ‖b n h‖ ≤ B)
    (hlim : ∀ h, Tendsto (fun n => b n h) atTop (𝓝 0))
    (hclassical : ∀ n h R, ‖Λ n (classicalTranslation h R) -
      classicalTranslation (Real.sqrt g • h) (Λ n R)‖ ≤ b n h * ‖R‖)
    (hquantum : ∀ z R, Tendsto (fun n =>
      ‖Λ n (quantumL1Action z R) - quantumL1Action (Real.sqrt g • z) (Λ n R)‖)
        atTop (𝓝 0)) :
    ∃ Γ : TraceClass (Fock s) →ₗ[ℂ] TraceClass (Fock s),
      IsCompletelyPositive Γ ∧
      (∀ X, 0 ≤ X.1 → (traceCLM (Γ X)).re ≤
        Thermal.classicalBase g ^ ((k : ℝ) / 2) * (traceCLM X).re) ∧
      (∀ z X, Γ (displacementTraceMap z X) =
        displacementTraceMap (Real.sqrt g • z) (Γ X)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ X (O : Fock s →L[ℂ] Fock s), IsCompactOperator O →
          Tendsto (fun n => tracePairing
            (weightedQuantumMap (Λ (φ n)).toLinearMap (GaussianAffinity.productDensity a)
              (GaussianAffinity.integrable_productDensity a ha)
              (GaussianAffinity.productWitness a (fun i => a i / g)) hχ hχbound X) O)
            atTop (𝓝 (tracePairing (Γ X) O)) := by
  let G := GaussianAffinity.productDensity a
  let χ := GaussianAffinity.productWitness a (fun i => a i / g)
  let hG := GaussianAffinity.integrable_productDensity a ha
  let L := fun n => weightedQuantumMap (Λ n).toLinearMap G hG χ hχ hχbound
  have hG0 := GaussianAffinity.productDensity_nonneg a
  have hG1 : ∫ y, G y = 1 := GaussianAffinity.integral_productDensity a ha
  have hχ0 (y : Fin k → ℝ) : 0 ≤ χ y :=
    (GaussianAffinity.productWitness_pos a _ ha
      (fun i => div_pos (ha i) (lt_of_lt_of_le zero_lt_one hg)) y).le
  have hCP (n : ℕ) : IsCompletelyPositive (L n) :=
    weightedQuantumMap_completelyPositive _ (hΛ n) G hG hG0 χ hχ hχ0 hχbound
  have htrace (n : ℕ) (X : TraceClass (Fock s)) (hX : 0 ≤ X.1) :
      (traceCLM (L n X)).re ≤ C * (traceCLM X).re :=
    weightedQuantumMap_trace_le _ (hΛ n) (hTP n) G hG hG0 hG1 χ hχ hχbound X hX
  have hdef (z : Fin s → ℂ) (X : TraceClass (Fock s)) :
      Tendsto (fun n => ‖L n (sandwichCLM (displacement z) (star (displacement z)) X) -
        sandwichCLM (displacement (Real.sqrt g • z)) (star (displacement (Real.sqrt g • z)))
          (L n X)‖) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
      displacementTraceMap] using weightedQuantumMap_weyl_defect_tendsto
        (fun n => (Λ n).toLinearMap) (Real.sqrt g) G hG χ hχ hχbound hquantum z X
  obtain ⟨Γ, hΓ, _, hcov, φ, hφ, hcoeff, hcompact⟩ :=
    exists_subsequence_covariant_completelyPositive_limit L C hC hCP htrace
      displacement (fun z => displacement (Real.sqrt g • z)) hdef
  refine ⟨Γ, hΓ, ?_, ?_, φ, hφ, hcompact⟩
  · intro X hX
    apply InfiniteTraceClassAsymptoticBound.trace_le_of_diagonal_tendsto
      (fun n => L (φ n) X) (Γ X) (fun n => (hCP (φ n)).map_nonneg X hX)
      (hΓ.map_nonneg X hX) (Thermal.classicalBase g ^ ((k : ℝ) / 2) * (traceCLM X).re)
      (fun x => hcoeff X x x)
    intro ε hε
    have ht : 0 ≤ (traceCLM X).re := trace_re_nonneg hX X.2
    have hd : 0 < (traceCLM X).re + 1 := by linarith
    have he := eventually_weightedQuantumMap_gaussian_trace_le Λ hΛ hTP a ha hg hχ hC
      hχbound b hb hbbound hlim hclassical (ε / ((traceCLM X).re + 1)) (div_pos hε hd)
    filter_upwards [hφ.tendsto_atTop.eventually he] with n hn
    apply (hn X hX).trans
    have hmul : ε / ((traceCLM X).re + 1) * (traceCLM X).re ≤ ε := by
      calc
        _ ≤ ε / ((traceCLM X).re + 1) * ((traceCLM X).re + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos hε hd).le
        _ = ε := div_mul_cancel₀ _ hd.ne'
    nlinarith
  · simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
      displacementTraceMap] using hcov

end Cloning.Hybrid
