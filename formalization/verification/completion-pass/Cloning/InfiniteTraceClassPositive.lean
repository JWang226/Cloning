import Cloning.InfiniteTraceClassAlgebra
import Cloning.InfiniteDensityState

/-! Positive trace-class operators, their analytic trace, and square roots on an arbitrary
complete complex Hilbert space. These results use the actual trace-class norm. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace
open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma inner_eq_real_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) (x : H) :
    ⟪x, A x⟫_ℂ = ((⟪x, A x⟫_ℂ).re : ℂ) := by
  have hx := (ContinuousLinearMap.isPositive_iff_complex A).mp
    (A.nonneg_iff_isPositive.mp hA) x
  have hs : ⟪A x, x⟫_ℂ = ⟪x, A x⟫_ℂ := by
    exact (A.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isSymmetric x x
  exact hs.symm.trans (hx.1.symm.trans (congrArg (fun r : ℝ => (r : ℂ))
    (congrArg Complex.re hs)))

lemma trace_eq_traceNorm_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) : trace A hTC = (traceNorm A hTC : ℂ) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis hTC b, traceNorm_eq_of_hilbertBasis hTC b,
    CFC.abs_of_nonneg A hA, Complex.ofReal_tsum]
  exact tsum_congr fun i => inner_eq_real_of_nonneg hA (b i)

lemma trace_re_eq_traceNorm {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) : (trace A hTC).re = traceNorm A hTC := by
  rw [trace_eq_traceNorm_of_nonneg hA hTC, Complex.ofReal_re]

lemma trace_im_eq_zero {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) : (trace A hTC).im = 0 := by
  rw [trace_eq_traceNorm_of_nonneg hA hTC, Complex.ofReal_im]

lemma trace_re_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) : 0 ≤ (trace A hTC).re := by
  rw [trace_re_eq_traceNorm hA hTC]
  exact traceNorm_nonneg A hTC

lemma isHilbertSchmidt_sqrt {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) : IsHilbertSchmidt (CFC.sqrt A) := by
  simpa only [CFC.abs_of_nonneg A hA] using
    isHilbertSchmidt_sqrt_abs_of_isTraceClass hTC

lemma tsum_sqrt_norm_sq_eq_trace_re {A : H →L[ℂ] H} (hA : 0 ≤ A)
    (hTC : IsTraceClass A) {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖CFC.sqrt A (b i)‖ ^ 2) = (trace A hTC).re := by
  rw [trace_re_eq_traceNorm hA hTC]
  simpa only [CFC.abs_of_nonneg A hA] using
    tsum_sqrt_abs_norm_sq_eq_traceNorm hTC b

lemma isTraceClass_abs {A : H →L[ℂ] H} (hA : IsTraceClass A) :
    IsTraceClass (CFC.abs A) := by
  have h := isTraceClass_mul_mul (A := star (Polar.polarFactor A)) (B := 1) hA
  simpa only [mul_one, Polar.star_polarFactor_mul_self] using h

lemma traceNorm_abs {A : H →L[ℂ] H} (hA : IsTraceClass A) :
    traceNorm (CFC.abs A) (isTraceClass_abs hA) = traceNorm A hA := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis _ b, traceNorm_eq_of_hilbertBasis hA b,
    CFC.abs_of_nonneg _ (CFC.abs_nonneg A)]

private lemma traceNorm_star_le {A : H →L[ℂ] H} (hA : IsTraceClass A) :
    traceNorm (star A) (isTraceClass_star hA) ≤ traceNorm A hA := by
  let U := Polar.polarFactor A
  have hU : ‖U‖ ≤ 1 := Polar.polarFactor_opNorm_le A
  have hfactor : CFC.abs A * star U = star A := by
    have h := congrArg star (Polar.polarFactor_mul_absOperator A)
    simpa only [Polar.absOperator, star_mul,
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg A)).star_eq] using h
  have hbound := traceNorm_mul_mul_le (A := (1 : H →L[ℂ] H)) (B := star U)
    (isTraceClass_abs hA) (isTraceClass_mul_mul (isTraceClass_abs hA))
  simp only [one_mul, hfactor, traceNorm_abs hA, norm_star] at hbound
  calc
    traceNorm (star A) (isTraceClass_star hA) ≤ ‖(1 : H →L[ℂ] H)‖ * traceNorm A hA * ‖U‖ := hbound
    _ ≤ 1 * traceNorm A hA * 1 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le
        (traceNorm_nonneg A hA)) hU (norm_nonneg U)
        (mul_nonneg zero_le_one (traceNorm_nonneg A hA))
    _ = traceNorm A hA := by ring

lemma traceNorm_star {A : H →L[ℂ] H} (hA : IsTraceClass A) :
    traceNorm (star A) (isTraceClass_star hA) = traceNorm A hA := by
  apply le_antisymm (traceNorm_star_le hA)
  simpa only [star_star] using traceNorm_star_le (isTraceClass_star hA)

lemma trace_re_mono {A B : H →L[ℂ] H} (hA : IsTraceClass A)
    (hB : IsTraceClass B) (hAB : A ≤ B) : (trace A hA).re ≤ (trace B hB).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hsA := (summable_trace_diagonal_of_isTraceClass hA b).map
    Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
  have hsB := (summable_trace_diagonal_of_isTraceClass hB b).map
    Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
  rw [trace_eq_of_hilbertBasis hA b, trace_eq_of_hilbertBasis hB b,
    Complex.re_tsum (summable_trace_diagonal_of_isTraceClass hA b),
    Complex.re_tsum (summable_trace_diagonal_of_isTraceClass hB b)]
  exact hsA.tsum_le_tsum (fun i => real_inner_mono_of_le hAB (b i)) hsB

lemma abs_traceNorm_sub_le {A B : H →L[ℂ] H} (hA : IsTraceClass A)
    (hB : IsTraceClass B) (hAB : IsTraceClass (A - B)) :
    |traceNorm A hA - traceNorm B hB| ≤ traceNorm (A - B) hAB := by
  exact abs_norm_sub_norm_le (TraceClass.ofOperator A hA) (TraceClass.ofOperator B hB)

end
end Cloning.InfiniteTraceClass
