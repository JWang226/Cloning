import Cloning.InfiniteTraceClassCutoffConvergence
import Cloning.InfiniteTraceClassWeakLimit
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Compact

/-! Normal-part reconstruction of a positive bounded functional on bounded
operators. Its values on rank-one operators determine an actual positive
trace-class operator, whose trace can be smaller than the norm of the original
functional. No trace-class representing operator is assumed. -/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded sesquilinear form obtained by evaluating a functional on rank ones. -/
def normalPartForm (f : (H →L[ℂ] H) →L[ℂ] ℂ) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ H (H →L[ℂ] H) ℂ f).comp
    (InnerProductSpace.rankOne ℂ).flip

/-- The Riesz operator reconstructed from the rank-one values of `f`. -/
def normalPartOp (f : (H →L[ℂ] H) →L[ℂ] ℂ) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (normalPartForm f)).adjoint

/-- Reconstruction has the actual rank-one matrix coefficients, for any bounded functional. -/
lemma normalPart_inner (f : (H →L[ℂ] H) →L[ℂ] ℂ) (x y : H) :
    ⟪y, normalPartOp f x⟫_ℂ = f (InnerProductSpace.rankOne ℂ x y) := by
  rw [normalPartOp, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

lemma normalPart_nonneg (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ A, 0 ≤ A → 0 ≤ f A) : 0 ≤ normalPartOp f := by
  apply (normalPartOp f).nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hr : 0 ≤ f (InnerProductSpace.rankOne ℂ x x) :=
    hf _ ((InnerProductSpace.rankOne ℂ x x).nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self x))
  have hi : ⟪normalPartOp f x, x⟫_ℂ =
      star (f (InnerProductSpace.rankOne ℂ x x)) := by
    rw [← inner_conj_symm, normalPart_inner]
    rfl
  rw [hi]
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hr
  constructor
  · apply Complex.ext <;> simp [← him]
  · simpa using hre

lemma normalPart_finite_diagonal_le (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    {w : Set H} (b : HilbertBasis w ℂ H) (s : Finset w) :
    (∑ i ∈ s, (⟪b i, normalPartOp f (b i)⟫_ℂ).re) ≤ ‖f‖ := by
  have heq : (∑ i ∈ s, (⟪b i, normalPartOp f (b i)⟫_ℂ).re) =
      (f (basisProjection b s)).re := by
    simp [basisProjection, normalPart_inner, map_sum, Complex.re_sum]
  rw [heq]
  calc
    (f (basisProjection b s)).re ≤ ‖f (basisProjection b s)‖ := Complex.re_le_norm _
    _ ≤ ‖f‖ * ‖basisProjection b s‖ := f.le_opNorm _
    _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left
      (basisProjection_isStarProjection b s).norm_le (norm_nonneg _)
    _ = ‖f‖ := mul_one _

/-- Positivity and boundedness force the reconstructed operator to be trace class. -/
theorem normalPart_isTraceClass (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ A, 0 ≤ A → 0 ≤ f A) : IsTraceClass (normalPartOp f) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact InfiniteTraceClassWeakLimit.isTraceClass_of_finite_diagonal_bound
    (normalPart_nonneg f hf) b ‖f‖ (normalPart_finite_diagonal_le f b)

/-- The normal part can lose trace mass to the singular part of the functional. -/
theorem normalPart_trace_le (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ A, 0 ≤ A → 0 ≤ f A) :
    (trace (normalPartOp f) (normalPart_isTraceClass f hf)).re ≤ ‖f‖ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_re_eq_traceNorm (normalPart_nonneg f hf), traceNorm_eq_of_hilbertBasis _ b,
    CFC.abs_of_nonneg _ (normalPart_nonneg f hf)]
  exact Real.tsum_le_of_sum_le
    (fun i => real_inner_nonneg_of_nonneg (normalPart_nonneg f hf) (b i))
    (normalPart_finite_diagonal_le f b)

/-- The normal part as an element of the trace-class Banach space. -/
def normalPart (f : (H →L[ℂ] H) →L[ℂ] ℂ) (hf : ∀ A, 0 ≤ A → 0 ≤ f A) :
    TraceClass H := TraceClass.ofOperator (normalPartOp f) (normalPart_isTraceClass f hf)

/-- Multiplication by a fixed trace-class operator, with the bounded operator
as the variable, is continuous into the trace-class Banach space. -/
def traceClassRightMultiply (T : TraceClass H) : (H →L[ℂ] H) →L[ℂ] TraceClass H :=
  LinearMap.mkContinuous
    { toFun := fun O => TraceClass.ofOperator (T.1 * O)
        (by simpa using (isTraceClass_mul_mul (A := 1) (B := O) T.2))
      map_add' := by
        intro A B
        apply Subtype.ext
        change T.1 * (A + B) = T.1 * A + T.1 * B
        exact mul_add _ _ _
      map_smul' := by
        intro c A
        apply Subtype.ext
        change T.1 * (c • A) = c • (T.1 * A)
        simp }
    ‖T‖ (fun O => by
      change traceNorm (T.1 * O) _ ≤ traceNorm T.1 T.2 * ‖O‖
      have h := traceNorm_mul_mul_le (A := (1 : H →L[ℂ] H)) (B := O) T.2
        (isTraceClass_mul_mul T.2)
      simp only [one_mul] at h
      apply h.trans
      have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp)
      calc
        ‖(1 : H →L[ℂ] H)‖ * traceNorm T.1 T.2 * ‖O‖ ≤
            1 * traceNorm T.1 T.2 * ‖O‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (traceNorm_nonneg _ _)) (norm_nonneg _)
        _ = _ := by ring)

/-- The continuous trace pairing of a trace-class operator with bounded observables. -/
def tracePairing (T : TraceClass H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  traceCLM.comp (traceClassRightMultiply T)

lemma trace_rankOne_general (x y : H) :
    trace (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y) = ⟪y, x⟫_ℂ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis _ b]
  simpa only [InnerProductSpace.rankOne_apply, inner_smul_right] using
    b.tsum_inner_mul_inner y x

lemma tracePairing_rankOne (T : TraceClass H) (x y : H) :
    tracePairing T (InnerProductSpace.rankOne ℂ x y) = ⟪y, T.1 x⟫_ℂ := by
  have heq : traceClassRightMultiply T (InnerProductSpace.rankOne ℂ x y) =
      rankOneOperator (T.1 x) y := by
    apply Subtype.ext
    change T.1 * InnerProductSpace.rankOne ℂ x y = InnerProductSpace.rankOne ℂ (T.1 x) y
    rw [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne]
  change traceCLM (traceClassRightMultiply T (InnerProductSpace.rankOne ℂ x y)) = _
  rw [heq]
  exact trace_rankOne_general _ _

/-- The normal-part trace pairing agrees with the original functional on every rank one. -/
lemma normalPart_tracePairing_rankOne (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ A, 0 ≤ A → 0 ≤ f A) (x y : H) :
    tracePairing (normalPart f hf) (InnerProductSpace.rankOne ℂ x y) =
      f (InnerProductSpace.rankOne ℂ x y) := by
  rw [tracePairing_rankOne]
  exact normalPart_inner f x y

/-- Strong basis projections converge uniformly on every compact set of vectors. -/
lemma basisProjection_tendstoUniformlyOn {ι : Type*} (b : HilbertBasis ι ℂ H)
    {S : Set H} (hS : IsCompact S) :
    TendstoUniformlyOn (fun s : Finset ι => basisProjection b s) (fun x => x) atTop S := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htS, ht, hcover⟩ := hS.finite_cover_balls (show 0 < ε / 3 by positivity)
  have hevent : ∀ᶠ s : Finset ι in atTop, ∀ y ∈ t, dist (basisProjection b s y) y < ε / 3 := by
    rw [ht.eventually_all]
    intro y _
    exact (Metric.tendsto_nhds.mp (basisProjection_tendsto b y)) _ (by positivity)
  filter_upwards [hevent] with s hs
  intro x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, dist x y < ε / 3 := by
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcover hx
  have hcon : dist (basisProjection b s y) (basisProjection b s x) ≤ dist y x := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    calc
      ‖basisProjection b s (y - x)‖ ≤ ‖basisProjection b s‖ * ‖y - x‖ :=
        (basisProjection b s).le_opNorm _
      _ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right
        (basisProjection_isStarProjection b s).norm_le (norm_nonneg _)
      _ = ‖y - x‖ := one_mul _
  have hnet := hs y hy
  have htri := dist_triangle x y (basisProjection b s x)
  have htri' := dist_triangle y (basisProjection b s y) (basisProjection b s x)
  rw [dist_comm y x] at hcon
  rw [dist_comm (basisProjection b s y) y] at hnet
  linarith

/-- Every compact observable is approximated in operator norm by finite-basis
range truncations. Compactness, rather than a finite-rank density premise, is used. -/
lemma basisProjection_mul_tendsto {ι : Type*} (b : HilbertBasis ι ℂ H)
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    Tendsto (fun s : Finset ι => basisProjection b s * K) atTop (𝓝 K) := by
  have hc : IsCompact (closure (K '' Metric.closedBall (0 : H) 1)) :=
    hK.isCompact_closure_image_closedBall 1
  have hu := Metric.tendstoUniformlyOn_iff.mp (basisProjection_tendstoUniformlyOn b hc)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hu (ε / 2) (by positivity)] with s hs
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2)
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hmem : K x ∈ closure (K '' Metric.closedBall (0 : H) 1) :=
      subset_closure ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩
    have h := hs (K x) hmem
    change ‖basisProjection b s (K x) - K x‖ ≤ ε / 2
    rw [dist_eq_norm, norm_sub_rev] at h
    exact h.le
  · linarith

lemma basisProjection_mul_eq_sum_rankOne {ι : Type*} (b : HilbertBasis ι ℂ H)
    (s : Finset ι) (K : H →L[ℂ] H) :
    basisProjection b s * K = ∑ i ∈ s, InnerProductSpace.rankOne ℂ (b i) (K.adjoint (b i)) := by
  simp only [basisProjection, Finset.sum_mul, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp]

/-- The reconstructed trace-class operator agrees with the original bounded
positive functional on every compact observable. -/
theorem normalPart_tracePairing_compact (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ A, 0 ≤ A → 0 ≤ f A) (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    tracePairing (normalPart f hf) K = f K := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have heq (s : Finset w) :
      tracePairing (normalPart f hf) (basisProjection b s * K) = f (basisProjection b s * K) := by
    rw [basisProjection_mul_eq_sum_rankOne]
    simp only [map_sum, normalPart_tracePairing_rankOne]
  have hl := (tracePairing (normalPart f hf)).continuous.tendsto K |>.comp
    (basisProjection_mul_tendsto b K hK)
  have hr := f.continuous.tendsto K |>.comp (basisProjection_mul_tendsto b K hK)
  simp only [Function.comp_def, heq] at hl
  exact tendsto_nhds_unique hl hr

end
end Cloning.InfiniteTraceClass
