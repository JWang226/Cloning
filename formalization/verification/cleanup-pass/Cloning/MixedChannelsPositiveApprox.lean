import Cloning.MixedChannels
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Positive simple fields approximate every positive operator-valued L¹ class.
This uses the actual trace-class order and requires no measurable spectral choice. -/
noncomputable section
open scoped ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private instance traceClassOrder : PartialOrder (TraceClass H) :=
  PartialOrder.lift (fun A : TraceClass H => A.1) Subtype.val_injective

/-- A sequence of everywhere positive, integrable simple fields converges to any
positive L¹ input in the actual trace norm. -/
theorem PositiveL1.exists_simple_approx (A : PositiveL1 H μ) :
    ∃ (f : ℕ → SimpleFunc Ω (TraceClass H)) (hf : ∀ n, Integrable (f n) μ),
      (∀ n y, 0 ≤ (f n y).1) ∧
      Tendsto (fun n => (hf n).toL1 (f n)) atTop (𝓝 A.1) := by
  let a : {g : Lp (TraceClass H) 1 μ // 0 ≤ g} :=
    ⟨A.1, (Lp.coeFn_nonneg A.1).mp A.2⟩
  obtain ⟨x, hx, ht⟩ := mem_closure_iff_seq_limit.mp
    (Lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg 1 μ (TraceClass H)
      (by simp) a)
  choose g hg using hx
  have hgt : Tendsto (fun n => (g n).1.1) atTop (𝓝 A.1) := by
    have hv := continuous_subtype_val.tendsto a |>.comp ht
    change Tendsto (fun n => (x n).1) atTop (𝓝 A.1) at hv
    convert hv using 1
    funext n
    exact congrArg Subtype.val (hg n)
  choose f hf he using fun n =>
    Lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq (g n).2
  have hfi (n) : Integrable (f n) μ :=
    (L1.integrable_coeFn (g n).1.1).congr (he n)
  refine ⟨f, hfi, hf, ?_⟩
  have heq (n) : (hfi n).toL1 (f n) = (g n).1.1 := by
    apply Lp.ext
    exact ((hfi n).coeFn_toL1).trans (he n).symm
  simpa only [heq] using hgt

end Cloning.Hybrid
