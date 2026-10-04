import Cloning.InfiniteFidelityWeighted
import Cloning.InfiniteTraceClassChannels
import Cloning.InfiniteTraceClassSeries
import Cloning.InfiniteHilbertSchmidtPositive

/-!
# Powers–Størmer inequality in the analytic trace-class setting

The square roots of positive trace-class operators are compared in Hilbert–Schmidt
norm. The proof uses the positive common majorant `B + (A - B)⁺` and positivity
of Hilbert–Schmidt trace pairings, without assuming square-root continuity.
-/

namespace Cloning.InfinitePowersStormer

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder InnerProductSpace BigOperators
open InfiniteTraceClass InfiniteTraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Analytic trace of a product of two Hilbert–Schmidt operators. -/
def productTrace (R S : H →L[ℂ] H) (hR : IsHilbertSchmidt R)
    (hS : IsHilbertSchmidt S) : ℂ :=
  trace (R * S) (isTraceClass_mul_of_isHilbertSchmidt hR hS)

lemma productTrace_comm {R S : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    (hS : IsHilbertSchmidt S) : productTrace R S hR hS = productTrace S R hS hR := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  unfold productTrace
  rw [trace_eq_of_hilbertBasis _ b, trace_eq_of_hilbertBasis _ b]
  exact tsum_diagonal_mul_eq_tsum_diagonal_swap b b hR hS

lemma productTrace_sub_left {R S T : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    productTrace (R - S) T (isHilbertSchmidt_sub hR hS) hT =
      productTrace R T hR hT - productTrace S T hS hT := by
  have heq : TraceClass.ofOperator ((R - S) * T)
      (isTraceClass_mul_of_isHilbertSchmidt (isHilbertSchmidt_sub hR hS) hT) =
      TraceClass.ofOperator (R * T) (isTraceClass_mul_of_isHilbertSchmidt hR hT) -
      TraceClass.ofOperator (S * T) (isTraceClass_mul_of_isHilbertSchmidt hS hT) := by
    apply Subtype.ext
    exact sub_mul R S T
  have htrace := congrArg (traceCLM (H := H)) heq
  simpa only [map_sub, traceCLM_apply, productTrace] using htrace

lemma productTrace_sub_right {R S T : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    productTrace R (S - T) hR (isHilbertSchmidt_sub hS hT) =
      productTrace R S hR hS - productTrace R T hR hT := by
  rw [productTrace_comm hR (isHilbertSchmidt_sub hS hT),
    productTrace_sub_left hS hT hR, productTrace_comm hS hR,
    productTrace_comm hT hR]

lemma productTrace_sqrt_self {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTA : IsTraceClass A) :
    productTrace (CFC.sqrt A) (CFC.sqrt A) (isHilbertSchmidt_sqrt hA hTA)
      (isHilbertSchmidt_sqrt hA hTA) = trace A hTA := by
  simp only [productTrace, CFC.sqrt_mul_sqrt_self A hA]

lemma productTrace_self_eq_hilbertSchmidt_square {R : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hRstar : IsSelfAdjoint R)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (productTrace R R hR hR).re = ∑' i : w, ‖R (b i)‖ ^ 2 := by
  have h := InfiniteFidelity.trace_re_star_mul_self hR b
  simpa only [hRstar.star_eq] using h

/-- The common positive majorant whose trace excess is exactly the trace norm
of the difference. This is built from the actual Jordan decomposition. -/
lemma exists_positive_traceClass_majorant {A B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    ∃ C : TraceClass H, 0 ≤ C.1 ∧ A ≤ C.1 ∧ B ≤ C.1 ∧
      2 * (trace C.1 C.2).re - (trace A hTA).re - (trace B hTB).re =
        ‖TraceClass.ofOperator A hTA - TraceClass.ofOperator B hTB‖ := by
  let a := TraceClass.ofOperator A hTA
  let b := TraceClass.ofOperator B hTB
  let d : TraceClass H := a - b
  have hd : IsSelfAdjoint d.1 := (IsSelfAdjoint.of_nonneg hA).sub
    (IsSelfAdjoint.of_nonneg hB)
  let p := TraceClass.positivePart d hd
  let q := TraceClass.negativePart d hd
  have hp : 0 ≤ p.1 := TraceClass.positivePart_nonneg d hd
  have hq : 0 ≤ q.1 := TraceClass.negativePart_nonneg d hd
  refine ⟨b + p, add_nonneg hB hp, ?_, ?_, ?_⟩
  · change A ≤ B + (A - B)⁺
    calc
      A = B + (A - B) := by abel
      _ ≤ B + (A - B)⁺ := add_le_add (le_refl B) (CFC.le_posPart hd)
  · exact le_add_of_nonneg_right hp
  · have hdecomp : p - q = a - b := TraceClass.positivePart_sub_negativePart d hd
    have ht := congrArg (fun X : TraceClass H => (traceCLM X).re) hdecomp
    simp only [map_sub, Complex.sub_re] at ht
    have hm : ‖p‖ + ‖q‖ = ‖d‖ := TraceClass.norm_positivePart_add_norm_negativePart d hd
    rw [TraceClass.norm_eq_trace_re_of_nonneg p hp,
      TraceClass.norm_eq_trace_re_of_nonneg q hq] at hm
    change (traceCLM p).re + (traceCLM q).re = ‖a - b‖ at hm
    change 2 * (traceCLM (b + p)).re - (traceCLM a).re - (traceCLM b).re = ‖a - b‖
    rw [map_add, Complex.add_re]
    linarith

/-- Positivity of three trace pairings bounds the square-root overlap below
by the traces and the trace of any common positive majorant. -/
lemma sqrt_overlap_ge_of_majorant {A B C : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) (hTC : IsTraceClass C)
    (hAC : A ≤ C) (hBC : B ≤ C) :
    (trace A hTA).re + (trace B hTB).re - (trace C hTC).re ≤
      (productTrace (CFC.sqrt A) (CFC.sqrt B)
        (isHilbertSchmidt_sqrt hA hTA) (isHilbertSchmidt_sqrt hB hTB)).re := by
  have ha := isHilbertSchmidt_sqrt hA hTA
  have hb := isHilbertSchmidt_sqrt hB hTB
  have hc := isHilbertSchmidt_sqrt hC hTC
  have hca := isHilbertSchmidt_sub hc ha
  have hcb := isHilbertSchmidt_sub hc hb
  have hca0 : 0 ≤ CFC.sqrt C - CFC.sqrt A := sub_nonneg.mpr (CFC.sqrt_le_sqrt A C hAC)
  have hcb0 : 0 ≤ CFC.sqrt C - CFC.sqrt B := sub_nonneg.mpr (CFC.sqrt_le_sqrt B C hBC)
  have hmain := trace_re_mul_nonneg_of_isHilbertSchmidt hca hcb hca0 hcb0
  have hleft := trace_re_mul_nonneg_of_isHilbertSchmidt hca ha hca0 (CFC.sqrt_nonneg A)
  have hright := trace_re_mul_nonneg_of_isHilbertSchmidt hcb hb hcb0 (CFC.sqrt_nonneg B)
  change 0 ≤ (productTrace _ _ hca hcb).re at hmain
  change 0 ≤ (productTrace _ _ hca ha).re at hleft
  change 0 ≤ (productTrace _ _ hcb hb).re at hright
  rw [productTrace_sub_left hc ha hcb, productTrace_sub_right hc hc hb,
    productTrace_sub_right ha hc hb, productTrace_comm ha hc] at hmain
  rw [productTrace_sub_left hc ha ha] at hleft
  rw [productTrace_sub_left hc hb hb] at hright
  rw [productTrace_sqrt_self hC hTC] at hmain
  rw [productTrace_sqrt_self hA hTA] at hleft
  rw [productTrace_sqrt_self hB hTB] at hright
  simp only [Complex.sub_re] at hmain hleft hright
  linarith

/-- Trace-class membership of a difference, derived from the Banach-space operations. -/
lemma isTraceClass_sub {A B : H →L[ℂ] H} (hA : IsTraceClass A) (hB : IsTraceClass B) :
    IsTraceClass (A - B) :=
  (TraceClass.ofOperator A hA - TraceClass.ofOperator B hB).2

/-- Powers–Størmer: the squared Hilbert–Schmidt distance between positive
square roots is bounded by the actual analytic trace norm of the difference. -/
theorem sqrt_hilbertSchmidt_square_le_traceNorm {A B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖(CFC.sqrt A - CFC.sqrt B) (b i)‖ ^ 2) ≤
      traceNorm (A - B) (isTraceClass_sub hTA hTB) := by
  obtain ⟨C, hC, hAC, hBC, hmass⟩ := exists_positive_traceClass_majorant hA hB hTA hTB
  have hoverlap := sqrt_overlap_ge_of_majorant hA hB hC hTA hTB C.2 hAC hBC
  have ha := isHilbertSchmidt_sqrt hA hTA
  have hb := isHilbertSchmidt_sqrt hB hTB
  have hd := isHilbertSchmidt_sub ha hb
  have hdstar : IsSelfAdjoint (CFC.sqrt A - CFC.sqrt B) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).sub
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B))
  rw [← productTrace_self_eq_hilbertSchmidt_square hd hdstar b,
    productTrace_sub_left ha hb hd, productTrace_sub_right ha ha hb,
    productTrace_sub_right hb ha hb, productTrace_comm hb ha]
  rw [productTrace_sqrt_self hA hTA, productTrace_sqrt_self hB hTB]
  simp only [Complex.sub_re]
  change 2 * (trace C.1 C.2).re - (trace A hTA).re - (trace B hTB).re =
    traceNorm (A - B) (isTraceClass_sub hTA hTB) at hmass
  linarith

end
end Cloning.InfinitePowersStormer
