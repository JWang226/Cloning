import Cloning.HybridWeightedTrace
import Cloning.WeylMultimodeChannel

/-! Fibrewise quantum displacement on the actual operator-valued L1 space,
and its passage through preparation and weighted quantum extraction. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bounded integration of an L1 quantum density against a scalar weight. -/
def weightedL1IntegralCLM (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) :
    Lp (TraceClass H) 1 μ →L[ℂ] TraceClass H :=
  (weightedL1Integral χ hχ hbound).mkContinuous C
    (norm_weightedL1Integral_le χ hχ hbound)

@[simp] theorem weightedL1IntegralCLM_apply (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (A : Lp (TraceClass H) 1 μ) :
    weightedL1IntegralCLM χ hχ hbound A = weightedL1Integral χ hχ hbound A := rfl

theorem norm_weightedL1IntegralCLM_le (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖χ y‖ ≤ C) :
    ‖weightedL1IntegralCLM (H := H) χ hχ hbound‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_weightedL1Integral_le χ hχ hbound)

theorem prepareL1_compLp (T : TraceClass H →L[ℂ] TraceClass K)
    (g : Ω → ℝ) (hg : Integrable g μ) (A : TraceClass H) :
    prepareL1 g hg (T A) = T.compLpL 1 μ (prepareL1 g hg A) := by
  apply Lp.ext
  filter_upwards [prepareL1_ae g hg (T A), T.coeFn_compLpL (prepareL1 g hg A),
    prepareL1_ae g hg A] with y h₁ h₂ h₃
  rw [h₁, h₂, h₃, map_smul]

theorem weightedL1Integral_compLp (T : TraceClass H →L[ℂ] TraceClass K)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (A : Lp (TraceClass H) 1 μ) :
    weightedL1Integral χ hχ hbound (T.compLpL 1 μ A) =
      T (weightedL1Integral χ hχ hbound A) := by
  change (∫ y, (χ y : ℂ) • (T.compLpL 1 μ A) y ∂μ) =
    T (∫ y, (χ y : ℂ) • A y ∂μ)
  rw [← T.integral_comp_comm (weightedL1_integrable χ hχ hbound A)]
  apply integral_congr_ae
  filter_upwards [T.coeFn_compLpL A] with y hy
  rw [hy, map_smul]

theorem norm_prepareL1 (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) (hprob : ∫ y, g y ∂μ = 1) (A : TraceClass H) :
    ‖prepareL1 g hg A‖ = ‖A‖ := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ y, g y * ‖A‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [prepareL1_ae g hg A] with y hy
      rw [hy, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hg0 y)]
    _ = _ := by rw [integral_mul_const, hprob, one_mul]

open Cloning.MultimodeCoherent
variable {s : ℕ}

/-- The actual Weyl action in every quantum fibre of the L1 register. -/
def quantumL1Action (z : Fin s → ℂ) :
    Lp (TraceClass (Fock s)) 1 μ →L[ℂ] Lp (TraceClass (Fock s)) 1 μ :=
  (displacementTraceMap z).compLpL 1 μ

theorem quantumL1Action_ae (z : Fin s → ℂ) (A : Lp (TraceClass (Fock s)) 1 μ) :
    quantumL1Action z A =ᵐ[μ] fun y => displacementTraceMap z (A y) :=
  (displacementTraceMap z).coeFn_compLpL A

theorem norm_quantumL1Action (z : Fin s → ℂ) (A : Lp (TraceClass (Fock s)) 1 μ) :
    ‖quantumL1Action z A‖ = ‖A‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [quantumL1Action_ae z A] with y hy
  rw [hy, displacementTraceMap_norm]

theorem quantumL1Action_add (z w : Fin s → ℂ) (A : Lp (TraceClass (Fock s)) 1 μ) :
    quantumL1Action (z + w) A = quantumL1Action z (quantumL1Action w A) := by
  apply Lp.ext
  filter_upwards [quantumL1Action_ae (z + w) A,
    quantumL1Action_ae z (quantumL1Action w A), quantumL1Action_ae w A] with y h₁ h₂ h₃
  rw [h₁, h₂, h₃, displacementTraceMap_add]

@[simp] theorem quantumL1Action_zero (A : Lp (TraceClass (Fock s)) 1 μ) :
    quantumL1Action 0 A = A := by
  apply Lp.ext
  filter_upwards [quantumL1Action_ae 0 A] with y hy
  rw [hy]
  apply Subtype.ext
  ext v : 1
  change displacement 0 ((A y).1 (displacement (-0) v)) = (A y).1 v
  simp

/-- Preparation and weighted output integration give exact Weyl covariance
whenever the actual hybrid map is covariant in its quantum fibres. -/
theorem weightedQuantumMap_weyl_covariance
    (Λ : Lp (TraceClass (Fock s)) 1 μ →ₗ[ℂ] Lp (TraceClass (Fock s)) 1 μ) (r : ℝ)
    (hΛ : ∀ z A, Λ (quantumL1Action z A) = quantumL1Action (r • z) (Λ A))
    (g : Ω → ℝ) (hg : Integrable g μ)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) (z : Fin s → ℂ) (X : TraceClass (Fock s)) :
    weightedQuantumMap Λ g hg χ hχ hbound (displacementTraceMap z X) =
      displacementTraceMap (r • z) (weightedQuantumMap Λ g hg χ hχ hbound X) := by
  change weightedL1Integral χ hχ hbound (Λ (prepareL1 g hg (displacementTraceMap z X))) = _
  rw [prepareL1_compLp]
  change weightedL1Integral χ hχ hbound (Λ (quantumL1Action z (prepareL1 g hg X))) = _
  rw [hΛ]
  exact weightedL1Integral_compLp (displacementTraceMap (r • z)) χ hχ hbound _

/-- Quantitative covariance passes to the extracted quantum map with exactly
the norm of the classical weight, and no loss from preparation. -/
theorem weightedQuantumMap_weyl_error_le
    (Λ : Lp (TraceClass (Fock s)) 1 μ →ₗ[ℂ] Lp (TraceClass (Fock s)) 1 μ) (r : ℝ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y)
    (hprob : ∫ y, g y ∂μ = 1)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖χ y‖ ≤ C)
    (z : Fin s → ℂ) (b : ℝ)
    (herror : ∀ A, ‖Λ (quantumL1Action z A) - quantumL1Action (r • z) (Λ A)‖ ≤ b * ‖A‖)
    (X : TraceClass (Fock s)) :
    ‖weightedQuantumMap Λ g hg χ hχ hbound (displacementTraceMap z X) -
      displacementTraceMap (r • z) (weightedQuantumMap Λ g hg χ hχ hbound X)‖ ≤
      C * b * ‖X‖ := by
  change ‖weightedL1Integral χ hχ hbound (Λ (prepareL1 g hg (displacementTraceMap z X))) -
    displacementTraceMap (r • z) (weightedL1Integral χ hχ hbound (Λ (prepareL1 g hg X)))‖ ≤ _
  rw [prepareL1_compLp, ← weightedL1Integral_compLp, ← map_sub]
  calc
    _ ≤ C * ‖Λ (quantumL1Action z (prepareL1 g hg X)) -
        quantumL1Action (r • z) (Λ (prepareL1 g hg X))‖ :=
      norm_weightedL1Integral_le χ hχ hbound _
    _ ≤ C * (b * ‖prepareL1 g hg X‖) := mul_le_mul_of_nonneg_left (herror _) hC
    _ = _ := by rw [norm_prepareL1 g hg hg0 hprob]; ring

end Cloning.Hybrid
