import Cloning.HybridCovariantWeighted
import Cloning.HybridTranslation
import Cloning.WeylCovariantization

/-! Complete positivity, trace preservation and strong continuity of the
fibrewise quantum action, together with the full hybrid translation action. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : ℕ}

theorem quantumL1Action_completelyPositive (z : Fin s → ℂ) :
    L1CompletelyPositive (quantumL1Action (μ := μ) z).toLinearMap := by
  intro n A hA
  have he : ∀ᵐ y ∂μ, ∀ i j : Fin n,
      quantumL1Action z (A i j) y = displacementTraceMap z (A i j y) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => quantumL1Action_ae z (A i j)
  filter_upwards [he, hA] with y hy hp
  change BlockPositive (fun i j => quantumL1Action z (A i j) y)
  simp only [hy, displacementTraceMap_eq_channel]
  exact (displacementChannel z).completelyPositive n (fun i j => A i j y) hp

theorem quantumL1Action_tracePreserving (z : Fin s → ℂ) :
    L1TracePreserving (quantumL1Action (μ := μ) z).toLinearMap := by
  intro A
  apply integral_congr_ae
  filter_upwards [quantumL1Action_ae z A] with y hy
  change traceCLM (quantumL1Action z A y) = traceCLM (A y)
  rw [hy, displacementTraceMap_eq_channel]
  exact (displacementChannel z).trace_preserving _

/-- Strong continuity in the quantum displacement, in the genuine L1 norm. -/
theorem continuous_quantumL1Action (A : Lp (TraceClass (Fock s)) 1 μ) :
    Continuous (fun z => quantumL1Action z A) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (w : Fin s → ℂ) :
      ‖quantumL1Action w A - quantumL1Action z A‖ =
        ∫ y, ‖displacementTraceMap w (A y) - displacementTraceMap z (A y)‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (quantumL1Action w A) (quantumL1Action z A),
      quantumL1Action_ae w A, quantumL1Action_ae z A] with y hsub hw hz
    rw [hsub]
    simp only [Pi.sub_apply, hw, hz]
  simp_rw [he]
  have hi : Integrable (fun y => 2 * ‖A y‖) μ := (L1.integrable_coeFn A).norm.const_mul 2
  have hmeas (w : Fin s → ℂ) : AEStronglyMeasurable
      (fun y => ‖displacementTraceMap w (A y) - displacementTraceMap z (A y)‖) μ :=
    (((displacementTraceMap w).integrable_comp (L1.integrable_coeFn A)).sub
      ((displacementTraceMap z).integrable_comp (L1.integrable_coeFn A))).norm.aestronglyMeasurable
  have hb (w : Fin s → ℂ) (y : Ω) :
      ‖‖displacementTraceMap w (A y) - displacementTraceMap z (A y)‖‖ ≤ 2 * ‖A y‖ := by
    rw [norm_norm]
    calc
      _ ≤ ‖displacementTraceMap w (A y)‖ + ‖displacementTraceMap z (A y)‖ := norm_sub_le _ _
      _ = _ := by simp only [displacementTraceMap_norm]; ring
  have hl (y : Ω) : Tendsto
      (fun w => ‖displacementTraceMap w (A y) - displacementTraceMap z (A y)‖)
      (𝓝 z) (𝓝 (0 : ℝ)) := by
    simpa using (((continuous_displacementTraceMap (A y)).tendsto z).sub_const
      (displacementTraceMap z (A y))).norm
  simpa using tendsto_integral_filter_of_dominated_convergence (fun y => 2 * ‖A y‖)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun w => Eventually.of_forall (hb w))
    hi (Eventually.of_forall hl)

theorem continuous_quantumL1Action_joint :
    Continuous (fun p : (Fin s → ℂ) × Lp (TraceClass (Fock s)) 1 μ =>
      quantumL1Action p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h1 : Tendsto (fun q : (Fin s → ℂ) × Lp (TraceClass (Fock s)) 1 μ =>
      ‖q.2 - p.2‖) (𝓝 p) (𝓝 0) := by
    simpa using (continuous_snd.tendsto p |>.sub_const p.2).norm
  have h2 : Tendsto (fun q : (Fin s → ℂ) × Lp (TraceClass (Fock s)) 1 μ =>
      ‖quantumL1Action q.1 p.2 - quantumL1Action p.1 p.2‖) (𝓝 p) (𝓝 0) := by
    simpa using (((continuous_quantumL1Action p.2).comp continuous_fst).tendsto p |>.sub_const
      (quantumL1Action p.1 p.2)).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using h1.add h2)
  intro q
  calc
    _ ≤ ‖quantumL1Action q.1 q.2 - quantumL1Action q.1 p.2‖ +
        ‖quantumL1Action q.1 p.2 - quantumL1Action p.1 p.2‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ = _ := by rw [← map_sub, norm_quantumL1Action]

variable {k : ℕ}

theorem classicalTranslation_quantumL1Action_commute (h : Fin k → ℝ) (z : Fin s → ℂ)
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    classicalTranslation h (quantumL1Action z A) = quantumL1Action z (classicalTranslation h A) := by
  apply Lp.ext
  have he := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae (quantumL1Action_ae z A)
  filter_upwards [classicalTranslation_ae h (quantumL1Action z A),
    quantumL1Action_ae z (classicalTranslation h A), classicalTranslation_ae h A, he] with y h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

/-- Simultaneous classical translation and Weyl displacement on hybrid L1. -/
def hybridTranslation (ξ : (Fin k → ℝ) × (Fin s → ℂ)) :
    Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) →L[ℂ]
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) :=
  (quantumL1Action ξ.2).comp (classicalTranslation ξ.1).toContinuousLinearMap

@[simp] theorem hybridTranslation_apply (ξ : (Fin k → ℝ) × (Fin s → ℂ))
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    hybridTranslation ξ A = quantumL1Action ξ.2 (classicalTranslation ξ.1 A) := rfl

@[simp] theorem hybridTranslation_quantum (z : Fin s → ℂ)
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    hybridTranslation (0, z) A = quantumL1Action z A := by
  simp [hybridTranslation_apply]

@[simp] theorem hybridTranslation_classical (h : Fin k → ℝ)
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    hybridTranslation (h, 0) A = classicalTranslation h A := by
  simp [hybridTranslation_apply]

@[simp] theorem norm_hybridTranslation (ξ : (Fin k → ℝ) × (Fin s → ℂ))
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    ‖hybridTranslation ξ A‖ = ‖A‖ := by
  rw [hybridTranslation_apply, norm_quantumL1Action, norm_classicalTranslation]

@[simp] theorem hybridTranslation_zero
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    hybridTranslation 0 A = A := by
  simp [hybridTranslation_apply]

theorem hybridTranslation_add (ξ η : (Fin k → ℝ) × (Fin s → ℂ))
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    hybridTranslation (ξ + η) A = hybridTranslation ξ (hybridTranslation η A) := by
  simp only [hybridTranslation_apply, Prod.fst_add, Prod.snd_add,
    classicalTranslation_add, quantumL1Action_add, classicalTranslation_quantumL1Action_commute]

theorem hybridTranslation_completelyPositive (ξ : (Fin k → ℝ) × (Fin s → ℂ)) :
    L1CompletelyPositive (hybridTranslation ξ).toLinearMap := by
  intro n A hA
  exact quantumL1Action_completelyPositive ξ.2 n _
    (classicalTranslation_completelyPositive ξ.1 n A hA)

theorem hybridTranslation_tracePreserving (ξ : (Fin k → ℝ) × (Fin s → ℂ)) :
    L1TracePreserving (hybridTranslation ξ).toLinearMap := by
  intro A
  exact (quantumL1Action_tracePreserving ξ.2 (classicalTranslation ξ.1 A)).trans
    (classicalTranslation_tracePreserving ξ.1 A)

set_option backward.isDefEq.respectTransparency true in
theorem continuous_hybridTranslation_joint :
    Continuous (fun p : ((Fin k → ℝ) × (Fin s → ℂ)) ×
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) => hybridTranslation p.1 p.2) := by
  change Continuous (fun p : ((Fin k → ℝ) × (Fin s → ℂ)) ×
    Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) =>
      quantumL1Action p.1.2 (classicalTranslation p.1.1 p.2))
  have hc : Continuous (fun p : ((Fin k → ℝ) × (Fin s → ℂ)) ×
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) =>
        classicalTranslation p.1.1 p.2) :=
    (continuous_classicalTranslation_joint (H := Fock s) (k := k)).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h1 : Tendsto (fun q => ‖classicalTranslation q.1.1 q.2 -
      classicalTranslation p.1.1 p.2‖) (𝓝 p) (𝓝 (0 : ℝ)) := by
    simpa using ((hc.tendsto p).sub_const (classicalTranslation p.1.1 p.2)).norm
  have h2 : Tendsto (fun q : ((Fin k → ℝ) × (Fin s → ℂ)) ×
      Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) =>
      ‖quantumL1Action q.1.2 (classicalTranslation p.1.1 p.2) -
        quantumL1Action p.1.2 (classicalTranslation p.1.1 p.2)‖) (𝓝 p) (𝓝 (0 : ℝ)) := by
    have hq : Continuous (fun q : ((Fin k → ℝ) × (Fin s → ℂ)) ×
        Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ)) =>
        quantumL1Action q.1.2 (classicalTranslation p.1.1 p.2)) :=
      (continuous_quantumL1Action (classicalTranslation p.1.1 p.2)).comp
        (continuous_snd.comp continuous_fst)
    simpa using ((hq.tendsto p).sub_const
      (quantumL1Action p.1.2 (classicalTranslation p.1.1 p.2))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using h1.add h2)
  intro q
  calc
    _ ≤ ‖quantumL1Action q.1.2 (classicalTranslation q.1.1 q.2) -
          quantumL1Action q.1.2 (classicalTranslation p.1.1 p.2)‖ +
        ‖quantumL1Action q.1.2 (classicalTranslation p.1.1 p.2) -
          quantumL1Action p.1.2 (classicalTranslation p.1.1 p.2)‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ = _ := by rw [← map_sub, norm_quantumL1Action]

theorem continuous_hybridTranslation
    (A : Lp (TraceClass (Fock s)) 1 (volume : Measure (Fin k → ℝ))) :
    Continuous (fun ξ => hybridTranslation ξ A) := by
  have h := (continuous_hybridTranslation_joint (k := k) (s := s)).comp
    (continuous_id.prodMk (continuous_const (y := A)))
  exact h

end Cloning.Hybrid
