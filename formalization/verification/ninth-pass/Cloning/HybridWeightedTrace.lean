import Cloning.HybridWeightedMaps
import Cloning.InfiniteTraceBoundedMaps

/-! Trace and boundedness of the actual weighted quantum extraction map.
No continuity or operator-norm bound is assumed for the hybrid channel:
complete positivity and preservation of integrated trace suffice. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def L1TracePreserving
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ) : Prop :=
  ∀ A, (∫ y, traceCLM (Λ A y) ∂μ) = ∫ y, traceCLM (A y) ∂μ

theorem L1CompletelyPositive.map_nonneg
    {Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ}
    (hΛ : L1CompletelyPositive Λ) (A : Lp (TraceClass H) 1 μ)
    (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) : ∀ᵐ y ∂μ, 0 ≤ (Λ A y).1 := by
  have hi : ∀ᵐ y ∂μ, BlockPositive (fun _ _ : Fin 1 => A y) := by
    filter_upwards [hA] with y hy
    intro v
    simpa only [Fin.sum_univ_one] using
      ((A y).1.nonneg_iff_isPositive.mp hy).inner_nonneg_right (v 0)
  have ho := hΛ 1 (fun _ _ => A) hi
  filter_upwards [ho] with y hy
  apply nonneg_of_inner_nonneg
  intro v
  simpa only [Fin.sum_univ_one] using hy (fun _ => v)

theorem prepareL1_nonneg (g : Ω → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ y, 0 ≤ g y) (A : TraceClass H) (hA : 0 ≤ A.1) :
    ∀ᵐ y ∂μ, 0 ≤ (prepareL1 g hg A y).1 := by
  filter_upwards [prepareL1_ae g hg A] with y hy
  rw [hy]
  change 0 ≤ (g y : ℂ) • A.1
  rw [Complex.coe_smul]
  exact smul_nonneg (hg0 y) hA

theorem integral_trace_prepareL1 (g : Ω → ℝ) (hg : Integrable g μ)
    (hprob : ∫ y, g y ∂μ = 1) (A : TraceClass H) :
    (∫ y, traceCLM (prepareL1 g hg A y) ∂μ) = traceCLM A := by
  calc
    _ = ∫ y, (g y : ℂ) * traceCLM A ∂μ := by
      apply integral_congr_ae
      filter_upwards [prepareL1_ae g hg A] with y hy
      simp only [hy, map_smul, smul_eq_mul]
    _ = (∫ y, (g y : ℂ) ∂μ) * traceCLM A := integral_mul_const _ _
    _ = _ := by
      have he := Complex.ofRealCLM.integral_comp_comm hg
      change (∫ y, (g y : ℂ) ∂μ) = ((∫ y, g y ∂μ : ℝ) : ℂ) at he
      rw [he, hprob]
      simp

/-- Positivity and trace preservation give the finite uniform trace bound
needed for compact CP extraction. The sharper asymptotic Gaussian factor is
a separate translation estimate. -/
theorem weightedQuantumMap_trace_le
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ)
    (hΛ : L1CompletelyPositive Λ) (hTP : L1TracePreserving Λ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y)
    (hprob : ∫ y, g y ∂μ = 1)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    (traceCLM (weightedQuantumMap Λ g hg χ hχ hbound A)).re ≤
      C * (traceCLM A).re := by
  let B := Λ (prepareL1 g hg A)
  let T : TraceClass K →L[ℝ] ℝ := Complex.reCLM.comp (traceCLM.restrictScalars ℝ)
  have hBi := L1.integrable_coeFn B
  have hBp : ∀ᵐ y ∂μ, 0 ≤ (B y).1 :=
    hΛ.map_nonneg _ (prepareL1_nonneg g hg hg0 A hA)
  have he : (traceCLM (weightedQuantumMap Λ g hg χ hχ hbound A)).re =
      ∫ y, χ y * (traceCLM (B y)).re ∂μ := by
    change T (∫ y, (χ y : ℂ) • B y ∂μ) = _
    rw [← T.integral_comp_comm (weightedL1_integrable χ hχ hbound B)]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change (traceCLM ((χ y : ℂ) • B y)).re = _
      simp only [map_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he]
  calc
    _ ≤ ∫ y, C * (traceCLM (B y)).re ∂μ := by
      apply integral_mono_ae ((T.integrable_comp hBi).bdd_mul hχ (Eventually.of_forall hbound))
        ((T.integrable_comp hBi).const_mul C)
      filter_upwards [hBp] with y hy
      exact mul_le_mul_of_nonneg_right ((le_abs_self (χ y)).trans (hbound y))
        (trace_re_nonneg hy (B y).2)
    _ = C * (traceCLM A).re := by
      rw [integral_const_mul]
      congr 1
      have he := Complex.reCLM.integral_comp_comm (traceCLM.integrable_comp hBi)
      change (∫ y, (traceCLM (B y)).re ∂μ) = (∫ y, traceCLM (B y) ∂μ).re at he
      rw [he]
      change (∫ y, traceCLM (Λ (prepareL1 g hg A) y) ∂μ).re = _
      rw [hTP, integral_trace_prepareL1 g hg hprob]

/-- The weighted extraction is automatically a bounded map on the whole
complex trace class, including non-self-adjoint inputs. -/
theorem weightedQuantumMap_norm_le
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ)
    (hΛ : L1CompletelyPositive Λ) (hTP : L1TracePreserving Λ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y)
    (hprob : ∫ y, g y ∂μ = 1)
    (χ : Ω → ℝ) (hχ : AEStronglyMeasurable χ μ) (hχ0 : ∀ y, 0 ≤ χ y)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ‖χ y‖ ≤ C) (A : TraceClass H) :
    ‖weightedQuantumMap Λ g hg χ hχ hbound A‖ ≤ (2 * C) * ‖A‖ :=
  norm_map_le_two_mul_of_trace_bound _
    (weightedQuantumMap_completelyPositive Λ hΛ g hg hg0 χ hχ hχ0 hbound).map_nonneg hC
    (weightedQuantumMap_trace_le Λ hΛ hTP g hg hg0 hprob χ hχ hbound) A

end Cloning.Hybrid
