import Cloning.InfiniteTraceClassPositive
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Positive trace-class weak limits with possible trace loss

A weak-operator limit of positive trace-class operators with uniformly bounded
trace remains positive and trace class. Only an upper bound on its trace
survives: mass may escape to infinitely many occupation modes. The limit is
not assumed trace class. The proof passes each finite diagonal sum through
the limit and then uses bounded nonnegative partial sums.
-/

namespace Cloning.InfiniteTraceClassWeakLimit

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter InfiniteTraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {α : Type*} {l : Filter α} [l.NeBot]

omit [CompleteSpace H] in
/-- Positivity is closed under convergence of all quadratic matrix coefficients. -/
theorem nonneg_of_diagonal_tendsto (A : α → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ n, 0 ≤ A n)
    (hlim : ∀ x, Tendsto (fun n ↦ ⟪A n x, x⟫_ℂ) l (𝓝 ⟪T x, x⟫_ℂ)) :
    0 ≤ T := by
  apply T.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
  intro x
  have hnonneg : 0 ≤ ⟪T x, x⟫_ℂ := ge_of_tendsto (hlim x)
    (Eventually.of_forall fun n ↦ ((A n).nonneg_iff_isPositive.mp (hA n)).inner_nonneg_left x)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnonneg
  refine ⟨?_, hre⟩
  apply Complex.ext
  · simp
  · simpa using him

/-- Every finite diagonal sum of a positive trace-class operator is bounded
by its analytic trace. -/
theorem finite_diagonal_le_trace {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hTC : IsTraceClass T) {w : Set H} (b : HilbertBasis w ℂ H) (s : Finset w) :
    (∑ i ∈ s, (⟪b i, T (b i)⟫_ℂ).re) ≤ (trace T hTC).re := by
  rw [trace_re_eq_traceNorm hT hTC, traceNorm_eq_of_hilbertBasis hTC b,
    CFC.abs_of_nonneg T hT]
  have hs := summable_inner_abs_of_hilbertBasis hTC b
  rw [CFC.abs_of_nonneg T hT] at hs
  exact hs.sum_le_tsum s (fun i _ ↦
    (T.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right (b i))

/-- The finite-sum Fatou step needs only diagonal weak convergence. -/
theorem finite_diagonal_le_of_tendsto (A : α → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ n, 0 ≤ A n) (hTC : ∀ n, IsTraceClass (A n)) (C : ℝ)
    (hbound : ∀ n, (trace (A n) (hTC n)).re ≤ C)
    (hlim : ∀ x, Tendsto (fun n ↦ ⟪A n x, x⟫_ℂ) l (𝓝 ⟪T x, x⟫_ℂ))
    {w : Set H} (b : HilbertBasis w ℂ H) (s : Finset w) :
    (∑ i ∈ s, (⟪b i, T (b i)⟫_ℂ).re) ≤ C := by
  have hd (i : w) : Tendsto (fun n ↦ (⟪b i, A n (b i)⟫_ℂ).re) l
      (𝓝 (⟪b i, T (b i)⟫_ℂ).re) := by
    convert (Complex.continuous_re.tendsto _).comp (hlim (b i)) using 1
    · ext n; exact inner_re_symm (𝕜 := ℂ) (b i) (A n (b i))
    · congr 1; exact inner_re_symm (𝕜 := ℂ) (b i) (T (b i))
  have hsum := tendsto_finset_sum s (fun i _ ↦ hd i)
  exact le_of_tendsto hsum (Eventually.of_forall fun n ↦
    (finite_diagonal_le_trace (hA n) (hTC n) b s).trans (hbound n))

/-- A positive bounded operator whose finite diagonal sums are bounded is
trace class; this is the nonnegative-series form of Fatou's argument. -/
theorem isTraceClass_of_finite_diagonal_bound {T : H →L[ℂ] H} (hT : 0 ≤ T)
    {w : Set H} (b : HilbertBasis w ℂ H) (C : ℝ)
    (hbound : ∀ s : Finset w, (∑ i ∈ s, (⟪b i, T (b i)⟫_ℂ).re) ≤ C) :
    IsTraceClass T := by
  refine ⟨w, b, ?_⟩
  rw [CFC.abs_of_nonneg T hT]
  exact summable_of_sum_le
    (fun i ↦ (T.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right (b i)) hbound

/-- Diagonal weak limits preserve positivity and an upper trace bound,
without requiring the limit to be trace class in advance. -/
theorem traceClass_of_diagonal_tendsto (A : α → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ n, 0 ≤ A n) (hTC : ∀ n, IsTraceClass (A n)) (C : ℝ)
    (hbound : ∀ n, (trace (A n) (hTC n)).re ≤ C)
    (hlim : ∀ x, Tendsto (fun n ↦ ⟪A n x, x⟫_ℂ) l (𝓝 ⟪T x, x⟫_ℂ)) :
    0 ≤ T ∧ ∃ hT : IsTraceClass T, (trace T hT).re ≤ C := by
  have hT := nonneg_of_diagonal_tendsto A T hA hlim
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hb := finite_diagonal_le_of_tendsto A T hA hTC C hbound hlim b
  have hclass := isTraceClass_of_finite_diagonal_bound hT b C hb
  refine ⟨hT, hclass, ?_⟩
  rw [trace_re_eq_traceNorm hT hclass, traceNorm_eq_of_hilbertBasis hclass b,
    CFC.abs_of_nonneg T hT]
  exact Real.tsum_le_of_sum_le
    (fun i ↦ (T.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right (b i)) hb

/-- Weak-operator closure of the positive trace-class ball, permitting trace
loss. The source filter can describe a sequence, subnet, or general net. -/
theorem traceClass_of_weakOperator_tendsto (A : α → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ n, 0 ≤ A n) (hTC : ∀ n, IsTraceClass (A n)) (C : ℝ)
    (hbound : ∀ n, (trace (A n) (hTC n)).re ≤ C)
    (hlim : ∀ x y, Tendsto (fun n ↦ ⟪A n x, y⟫_ℂ) l (𝓝 ⟪T x, y⟫_ℂ)) :
    0 ≤ T ∧ ∃ hT : IsTraceClass T, (trace T hT).re ≤ C :=
  traceClass_of_diagonal_tendsto A T hA hTC C hbound (fun x ↦ hlim x x)

/-- Every escaping occupation projector still has trace exactly one. -/
theorem basis_projector_trace_one (b : HilbertBasis ℕ ℂ H) (n : ℕ) :
    trace (InnerProductSpace.rankOne ℂ (b n) (b n)) (isTraceClass_rankOne_self (b n)) = 1 := by
  rw [trace_rankOne_self, b.orthonormal.norm_eq_one n]
  simp

omit [CompleteSpace H] in
/-- Unit-trace basis projectors converge weakly to zero. This concrete
trace-loss example explains why the closure theorem concludes `trace ≤ C`. -/
theorem basis_projectors_weak_zero (b : HilbertBasis ℕ ℂ H) (x y : H) :
    Tendsto (fun n ↦ ⟪InnerProductSpace.rankOne ℂ (b n) (b n) x, y⟫_ℂ)
      atTop (𝓝 0) := by
  have h := (b.summable_inner_mul_inner x y).tendsto_atTop_zero
  simpa only [InnerProductSpace.rankOne_apply, inner_smul_left, inner_conj_symm] using h

end
end Cloning.InfiniteTraceClassWeakLimit
