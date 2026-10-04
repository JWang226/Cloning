import Cloning.HybridWeightedTrace
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Actual hybrid channels on operator-valued L¹. The uniform whole-space bound
is derived from complete positivity and integrated trace preservation, using
finite simple functions and density; no measurable Jordan-decomposition choice
is assumed. -/

noncomputable section
open scoped ComplexOrder Topology ENNReal
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_L1_eq_trace_re (A : Lp (TraceClass H) 1 μ)
    (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    ‖A‖ = (∫ y, traceCLM (A y) ∂μ).re := by
  rw [L1.norm_eq_integral_norm]
  change _ = Complex.reCLM (∫ y, traceCLM (A y) ∂μ)
  rw [← Complex.reCLM.integral_comp_comm (traceCLM.integrable_comp (L1.integrable_coeFn A))]
  apply integral_congr_ae
  filter_upwards [hA] with y hy
  exact TraceClass.norm_eq_trace_re_of_nonneg _ hy

lemma norm_L1_map_nonneg
    (Λ : Lp (TraceClass H) 1 μ →ₗ[ℂ] Lp (TraceClass K) 1 μ)
    (hCP : L1CompletelyPositive Λ) (hTP : L1TracePreserving Λ)
    (A : Lp (TraceClass H) 1 μ) (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    ‖Λ A‖ = ‖A‖ := by
  rw [norm_L1_eq_trace_re _ (hCP.map_nonneg A hA),
    norm_L1_eq_trace_re _ hA, hTP]

private lemma norm_map_selfAdjoint_of_positive_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : TraceClass H →ₗ[ℂ] E) {c : ℝ}
    (hp : ∀ A, 0 ≤ A.1 → ‖Φ A‖ ≤ c * ‖A‖)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) : ‖Φ A‖ ≤ c * ‖A‖ := by
  calc
    ‖Φ A‖ = ‖Φ (TraceClass.positivePart A hA) -
        Φ (TraceClass.negativePart A hA)‖ := by
      rw [← map_sub, TraceClass.positivePart_sub_negativePart A hA]
    _ ≤ ‖Φ (TraceClass.positivePart A hA)‖ +
        ‖Φ (TraceClass.negativePart A hA)‖ := norm_sub_le _ _
    _ ≤ c * ‖TraceClass.positivePart A hA‖ + c * ‖TraceClass.negativePart A hA‖ :=
      add_le_add (hp _ (TraceClass.positivePart_nonneg A hA))
        (hp _ (TraceClass.negativePart_nonneg A hA))
    _ = c * ‖A‖ := by
      rw [← mul_add, TraceClass.norm_positivePart_add_norm_negativePart A hA]

lemma norm_map_two_mul_of_positive_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : TraceClass H →ₗ[ℂ] E) {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ A, 0 ≤ A.1 → ‖Φ A‖ ≤ c * ‖A‖) (A : TraceClass H) :
    ‖Φ A‖ ≤ (2 * c) * ‖A‖ := by
  calc
    ‖Φ A‖ = ‖Φ (TraceClass.realComponent A) +
        Complex.I • Φ (TraceClass.imaginaryComponent A)‖ := by
      conv_lhs => rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A]
      rw [map_add, map_smul]
    _ ≤ ‖Φ (TraceClass.realComponent A)‖ + ‖Φ (TraceClass.imaginaryComponent A)‖ := by
      simpa [norm_smul] using norm_add_le (Φ (TraceClass.realComponent A))
        (Complex.I • Φ (TraceClass.imaginaryComponent A))
    _ ≤ c * ‖TraceClass.realComponent A‖ + c * ‖TraceClass.imaginaryComponent A‖ :=
      add_le_add (norm_map_selfAdjoint_of_positive_bound Φ hp _
        (TraceClass.realComponent_isSelfAdjoint A))
        (norm_map_selfAdjoint_of_positive_bound Φ hp _
          (TraceClass.imaginaryComponent_isSelfAdjoint A))
    _ ≤ c * ‖A‖ + c * ‖A‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (TraceClass.norm_realComponent_le A) hc)
        (mul_le_mul_of_nonneg_left (TraceClass.norm_imaginaryComponent_le A) hc)
    _ = (2 * c) * ‖A‖ := by ring

private def indicatorLinear {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    TraceClass H →ₗ[ℂ] Lp (TraceClass H) 1 μ where
  toFun A := indicatorConstLp 1 hs hμs A
  map_add' A B := indicatorConstLp_add.symm
  map_smul' c A := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (c := c • A),
      indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := A),
      Lp.coeFn_smul c (indicatorConstLp 1 hs hμs A)] with y hy hz hw
    change _ = (c • indicatorConstLp 1 hs hμs A) y
    rw [hy, hw, Pi.smul_apply, hz]
    by_cases h : y ∈ s <;> simp [h]

private lemma indicatorLinear_nonneg {s : Set Ω} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (A : TraceClass H) (hA : 0 ≤ A.1) :
    ∀ᵐ y ∂μ, 0 ≤ (indicatorLinear hs hμs A y).1 := by
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := A)] with y hy
  change 0 ≤ (indicatorConstLp 1 hs hμs A y).1
  rw [hy]
  by_cases h : y ∈ s <;> simp [h, hA]

/-- Complete positivity and trace preservation give one bound for every
continuous hybrid competitor, independent of that competitor. -/
theorem L1CompletelyPositive.norm_le_two
    (Λ : Lp (TraceClass H) 1 μ →L[ℂ] Lp (TraceClass K) 1 μ)
    (hCP : L1CompletelyPositive Λ.toLinearMap) (hTP : L1TracePreserving Λ.toLinearMap)
    (A : Lp (TraceClass H) 1 μ) : ‖Λ A‖ ≤ 2 * ‖A‖ := by
  refine Lp.induction (p := 1) (by simp) (fun A => ‖Λ A‖ ≤ 2 * ‖A‖) ?_ ?_ ?_ A
  · intro c s hs hμs
    have hp : ∀ B : TraceClass H, 0 ≤ B.1 →
        ‖(Λ.toLinearMap.comp (indicatorLinear hs hμs.ne)) B‖ ≤ μ.real s * ‖B‖ := by
      intro B hB
      rw [LinearMap.comp_apply, norm_L1_map_nonneg Λ.toLinearMap hCP hTP _
        (indicatorLinear_nonneg hs hμs.ne B hB)]
      change ‖indicatorConstLp 1 hs hμs.ne B‖ ≤ _
      simp [norm_indicatorConstLp (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp), mul_comm]
    have h := norm_map_two_mul_of_positive_bound
      (Λ.toLinearMap.comp (indicatorLinear hs hμs.ne)) ENNReal.toReal_nonneg hp c
    simpa [indicatorLinear, norm_indicatorConstLp (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp),
      mul_comm, mul_left_comm, mul_assoc] using h
  · intro f g hf hg hfg hF hG
    have hn : ‖hf.toLp f + hg.toLp g‖ = ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
      rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
        ← integral_add (L1.integrable_coeFn (hf.toLp f)).norm
          (L1.integrable_coeFn (hg.toLp g)).norm]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
        with y hy hfy hgy
      rw [hy, Pi.add_apply, hfy, hgy]
      have hd : f y = 0 ∨ g y = 0 := by
        by_cases h : f y = 0
        · exact Or.inl h
        · exact Or.inr (by
            by_contra hh
            exact Set.disjoint_left.mp hfg h hh)
      rcases hd with h | h <;> simp [h]
    rw [map_add, hn, mul_add]
    exact (norm_add_le _ _).trans (add_le_add hF hG)
  · exact isClosed_le Λ.continuous.norm (continuous_const.mul continuous_norm)

/-- A channel acting on the genuine classical–quantum L¹ space. -/
structure Channel (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (μ : Measure Ω) where
  map : Lp (TraceClass H) 1 μ →L[ℂ] Lp (TraceClass K) 1 μ
  completelyPositive : L1CompletelyPositive map.toLinearMap
  tracePreserving : L1TracePreserving map.toLinearMap

lemma Channel.norm_le_two (Λ : Channel H K μ) (A : Lp (TraceClass H) 1 μ) :
    ‖Λ.map A‖ ≤ 2 * ‖A‖ := Λ.completelyPositive.norm_le_two Λ.map Λ.tracePreserving A

lemma Channel.opNorm_le_two (Λ : Channel H K μ) : ‖Λ.map‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) Λ.norm_le_two

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Composition acts on actual L¹ equivalence classes. -/
def Channel.comp (Λ : Channel K J μ) (Γ : Channel H K μ) : Channel H J μ where
  map := Λ.map.comp Γ.map
  completelyPositive := fun n A hA => Λ.completelyPositive n _ (Γ.completelyPositive n A hA)
  tracePreserving := fun A => (Λ.tracePreserving (Γ.map A)).trans (Γ.tracePreserving A)

@[simp] lemma Channel.comp_apply (Λ : Channel K J μ) (Γ : Channel H K μ)
    (A : Lp (TraceClass H) 1 μ) : (Λ.comp Γ).map A = Λ.map (Γ.map A) := rfl

end Cloning.Hybrid
