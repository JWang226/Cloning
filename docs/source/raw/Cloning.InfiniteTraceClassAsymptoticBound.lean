import Cloning.InfiniteTraceClassWeakLimit
import Cloning.InfiniteTraceClassSeries
import Mathlib.Order.LiminfLimsup

/-!
# Asymptotic trace bounds for actual weak operator limits

The trace of a positive trace-class weak limit is bounded by an eventual
`C + ε` bound on source traces. No continuity of the trace in weak operator
topology is assumed. The argument passes finite nonnegative diagonal sums
through the limit, then takes their supremum. An actual scalar limsup bound
supplies the needed eventual bounds.
-/

namespace Cloning.InfiniteTraceClassAsymptoticBound

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter InfiniteTraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {α : Type*} {l : Filter α} [l.NeBot]

/-- An eventual asymptotic trace bound controls the trace of a positive weak
limit. Diagonal convergence suffices; full WOT convergence is stronger. -/
theorem trace_le_of_diagonal_tendsto (A : α → TraceClass H) (T : TraceClass H)
    (hA : ∀ a, 0 ≤ (A a).1) (hT : 0 ≤ T.1) (C : ℝ)
    (hlim : ∀ x, Tendsto (fun a ↦ ⟪x, (A a).1 x⟫_ℂ) l (𝓝 ⟪x, T.1 x⟫_ℂ))
    (hbound : ∀ ε > 0, ∀ᶠ a in l, (traceCLM (A a)).re ≤ C + ε) :
    (traceCLM T).re ≤ C := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hpartial (s : Finset w) : (∑ i ∈ s, (⟪b i, T.1 (b i)⟫_ℂ).re) ≤ C := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hsum : Tendsto (fun a ↦ ∑ i ∈ s, (⟪b i, (A a).1 (b i)⟫_ℂ).re) l
        (𝓝 (∑ i ∈ s, (⟪b i, T.1 (b i)⟫_ℂ).re)) :=
      tendsto_finset_sum s (fun i _ ↦ (Complex.continuous_re.tendsto _).comp (hlim (b i)))
    apply le_of_tendsto hsum
    filter_upwards [hbound ε hε] with a ha
    exact (InfiniteTraceClassWeakLimit.finite_diagonal_le_trace (hA a) (A a).2 b s).trans ha
  change (trace T.1 T.2).re ≤ C
  rw [trace_re_eq_traceNorm hT T.2, traceNorm_eq_of_hilbertBasis T.2 b,
    CFC.abs_of_nonneg T.1 hT]
  exact Real.tsum_le_of_sum_le
    (fun i ↦ (T.1.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right (b i)) hpartial

/-- The manuscript's scalar limsup premise implies the actual trace bound.
Only eventual upper boundedness of the scalar source traces is needed. -/
theorem trace_le_of_limsup_le (A : α → TraceClass H) (T : TraceClass H)
    (hA : ∀ a, 0 ≤ (A a).1) (hT : 0 ≤ T.1) (C : ℝ)
    (hlim : ∀ x, Tendsto (fun a ↦ ⟪x, (A a).1 x⟫_ℂ) l (𝓝 ⟪x, T.1 x⟫_ℂ))
    (hbounded : l.IsBoundedUnder (· ≤ ·) (fun a ↦ (traceCLM (A a)).re))
    (hlimsup : Filter.limsup (fun a ↦ (traceCLM (A a)).re) l ≤ C) :
    (traceCLM T).re ≤ C := by
  apply trace_le_of_diagonal_tendsto A T hA hT C hlim
  intro ε hε
  exact (eventually_lt_of_limsup_lt
    (hlimsup.trans_lt (lt_add_of_pos_right C hε)) hbounded).mono (fun _ h ↦ h.le)

/-- A globally bounded scalar trace range is a convenient sufficient
boundedness hypothesis for the limsup formulation. -/
theorem trace_le_of_limsup_le_of_bddAbove (A : α → TraceClass H) (T : TraceClass H)
    (hA : ∀ a, 0 ≤ (A a).1) (hT : 0 ≤ T.1) (C : ℝ)
    (hlim : ∀ x, Tendsto (fun a ↦ ⟪x, (A a).1 x⟫_ℂ) l (𝓝 ⟪x, T.1 x⟫_ℂ))
    (hbounded : BddAbove (Set.range (fun a ↦ (traceCLM (A a)).re)))
    (hlimsup : Filter.limsup (fun a ↦ (traceCLM (A a)).re) l ≤ C) :
    (traceCLM T).re ≤ C :=
  trace_le_of_limsup_le A T hA hT C hlim hbounded.isBoundedUnder_of_range hlimsup

end
end Cloning.InfiniteTraceClassAsymptoticBound
