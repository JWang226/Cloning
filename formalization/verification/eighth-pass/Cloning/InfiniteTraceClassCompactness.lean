import Cloning.InfiniteTraceClassNormalPart
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Sequences

/-! Actual subsequence extraction for positive trace-bounded operators on a
separable Hilbert space. Banach--Alaoglu supplies compactness; countably many
rank-one evaluations supply the subsequence. No extraction premise is assumed. -/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter TopologicalSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma norm_traceClassRightMultiply_le (T : TraceClass H) :
    ‖traceClassRightMultiply T‖ ≤ ‖T‖ := by
  unfold traceClassRightMultiply
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

lemma norm_tracePairing_le (T : TraceClass H) : ‖tracePairing T‖ ≤ ‖T‖ := by
  have ht : ‖(traceCLM : TraceClass H →L[ℂ] ℂ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simpa using norm_trace_le_traceNorm A.2
  calc
    ‖tracePairing T‖ ≤ ‖(traceCLM : TraceClass H →L[ℂ] ℂ)‖ * ‖traceClassRightMultiply T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul ht (norm_traceClassRightMultiply_le T)
      (norm_nonneg _) zero_le_one
    _ = ‖T‖ := one_mul _

/-- Uniformly bounded linear functionals converge at closure points whenever
they converge on the generating set. This is an explicit epsilon argument. -/
lemma tendsto_functionals_at_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℕ → E →L[ℂ] ℂ) (f : E →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (hf : ‖f‖ ≤ C) {S : Set E}
    (hpoint : ∀ x ∈ S, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {x : E} (hx : x ∈ closure S) : Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let D := 2 * C + 1
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / (3 * D)) (by positivity)
  have hevent := (Metric.tendsto_nhds.mp (hpoint y hy)) (ε / 3) (by positivity)
  filter_upwards [hevent] with n hn
  have hdiff : ‖u n - f‖ ≤ D := by
    have := norm_sub_le (u n) f
    dsimp [D]
    linarith [hu n]
  have hbound : ‖(u n - f) (x - y)‖ ≤ D * ‖x - y‖ :=
    ((u n - f).le_opNorm _).trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
  have heq : u n x - f x = (u n - f) (x - y) + (u n y - f y) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    ring
  rw [dist_eq_norm, heq]
  have htri := norm_add_le ((u n - f) (x - y)) (u n y - f y)
  rw [dist_eq_norm] at hn hxy
  have hsmall : D * ‖x - y‖ < ε / 3 := by
    have h := (mul_lt_mul_of_pos_left hxy hD)
    have hd : D * (ε / (3 * D)) = ε / 3 := by field_simp
    rwa [hd] at h
  linarith

/-- Bounded functionals have a subsequence converging on any countable family
of observables, with a genuine bounded functional as the limit. -/
theorem exists_subsequence_functionals_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℕ → E →L[ℂ] ℂ) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C)
    (O : ℕ × ℕ → E) :
    ∃ f : E →L[ℂ] ℂ, ‖f‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun n => u (φ n) (O i)) atTop (𝓝 (f (O i))) := by
  let B : Set (WeakDual ℂ E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C
  let ev : WeakDual ℂ E → (ℕ × ℕ → ℂ) := fun f i => f (O i)
  have hev : Continuous ev := continuous_pi (fun i => WeakDual.eval_continuous (O i))
  have hc : IsCompact B := WeakDual.isCompact_closedBall ℂ (0 : E →L[ℂ] ℂ) C
  have hmem (n : ℕ) : ev (StrongDual.toWeakDual (u n)) ∈ ev '' B := by
    refine ⟨StrongDual.toWeakDual (u n), ?_, rfl⟩
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hu n
  obtain ⟨g, hg, φ, hφ, hlim⟩ := (hc.image hev).tendsto_subseq hmem
  obtain ⟨f, hf, rfl⟩ := hg
  refine ⟨WeakDual.toStrongDual f, ?_, φ, hφ, ?_⟩
  · simpa [B, Metric.mem_closedBall, dist_zero_right] using hf
  · intro i
    exact (continuous_apply i).tendsto _ |>.comp hlim

/-- A trace-bounded positive sequence on a separable Hilbert space has an
actual weak-operator convergent subsequence. Its positive trace-class limit
can have smaller trace, so trace preservation is not asserted. -/
theorem exists_subsequence_weak_operator_limit [TopologicalSpace.SeparableSpace H]
    (A : ℕ → TraceClass H) (hA : ∀ n, 0 ≤ (A n).1) (C : ℝ)
    (htrace : ∀ n, (trace (A n).1 (A n).2).re ≤ C) :
    ∃ T : TraceClass H, 0 ≤ T.1 ∧ (trace T.1 T.2).re ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ x y : H,
        Tendsto (fun n => ⟪y, (A (φ n)).1 x⟫_ℂ) atTop (𝓝 ⟪y, T.1 x⟫_ℂ) := by
  let u : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ := fun n => tracePairing (A n)
  have hnorm (n : ℕ) : ‖A n‖ ≤ C := by
    rw [TraceClass.norm_eq_trace_re_of_nonneg _ (hA n)]
    exact htrace n
  have hu (n : ℕ) : ‖u n‖ ≤ C := (norm_tracePairing_le (A n)).trans (hnorm n)
  have hC : 0 ≤ C := (norm_nonneg (A 0)).trans (hnorm 0)
  let d := denseSeq H
  let O : ℕ × ℕ → H →L[ℂ] H := fun i => InnerProductSpace.rankOne ℂ (d i.1) (d i.2)
  obtain ⟨f, hf, φ, hφ, hlim⟩ := exists_subsequence_functionals_countable u C hu O
  have hrank (x y : H) : InnerProductSpace.rankOne ℂ x y ∈ closure (Set.range O) := by
    have hd : DenseRange (fun i : ℕ × ℕ => (d i.1, d i.2)) :=
      (denseRange_denseSeq H).prodMap (denseRange_denseSeq H)
    have hr : Continuous (fun p : H × H => InnerProductSpace.rankOne ℂ p.1 p.2) :=
      (ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp
        (((innerSL ℂ).continuous.comp continuous_snd).prodMk continuous_fst)
    have h := hr.range_subset_closure_image_dense hd ⟨(x, y), rfl⟩
    simpa only [← Set.range_comp, Function.comp_def, O] using h
  have hcoeff (x y : H) : Tendsto (fun n => ⟪y, (A (φ n)).1 x⟫_ℂ) atTop
      (𝓝 ⟪y, normalPartOp f x⟫_ℂ) := by
    have h := tendsto_functionals_at_closure (fun n => u (φ n)) f C hC
      (fun n => hu (φ n)) hf (S := Set.range O)
      (by rintro _ ⟨i, rfl⟩; exact hlim i) (hrank x y)
    simpa only [u, tracePairing_rankOne, normalPart_inner] using h
  have hdiag (x : H) : Tendsto (fun n => ⟪(A (φ n)).1 x, x⟫_ℂ) atTop
      (𝓝 ⟪normalPartOp f x, x⟫_ℂ) := by
    convert (hcoeff x x).star using 1
    · ext n; exact (inner_conj_symm _ _).symm
    · congr 1; exact (inner_conj_symm _ _).symm
  obtain ⟨hpos, hTC, hbound⟩ := InfiniteTraceClassWeakLimit.traceClass_of_diagonal_tendsto
    (fun n => (A (φ n)).1) (normalPartOp f) (fun n => hA (φ n))
    (fun n => (A (φ n)).2) C (fun n => htrace (φ n)) hdiag
  exact ⟨TraceClass.ofOperator (normalPartOp f) hTC, hpos, hbound, φ, hφ, hcoeff⟩

end
end Cloning.InfiniteTraceClass
