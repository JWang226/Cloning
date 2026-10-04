import Cloning.InfiniteTraceClassNormalPart

/-!
# Compact-observable convergence from weak operator convergence

Uniform trace-norm bounds and convergence of actual matrix coefficients imply
convergence of traces against every compact bounded observable. Finite-rank
approximation is proved using the Hilbert-basis projections of the compact
observable, rather than assumed as a density hypothesis.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem tracePairing_opNorm_le (T : TraceClass H) : ‖tracePairing T‖ ≤ ‖T‖ := by
  have ht : ‖(traceCLM : TraceClass H →L[ℂ] ℂ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simpa using norm_trace_le_traceNorm A.2
  have hmul : ‖traceClassRightMultiply T‖ ≤ ‖T‖ := by
    unfold traceClassRightMultiply
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    ‖tracePairing T‖ ≤ ‖(traceCLM : TraceClass H →L[ℂ] ℂ)‖ * ‖traceClassRightMultiply T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul ht hmul (norm_nonneg _) zero_le_one
    _ = ‖T‖ := one_mul _

/-- The closure argument for bounded functionals also works for arbitrary nets. -/
theorem tendsto_functionals_at_closure_filter {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Filter α)
    (u : α → E →L[ℂ] ℂ) (f : E →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (hf : ‖f‖ ≤ C) {S : Set E}
    (hpoint : ∀ x ∈ S, Tendsto (fun n => u n x) l (𝓝 (f x)))
    {x : E} (hx : x ∈ closure S) : Tendsto (fun n => u n x) l (𝓝 (f x)) := by
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
    have h := mul_lt_mul_of_pos_left hxy hD
    have hd : D * (ε / (3 * D)) = ε / 3 := by field_simp
    rwa [hd] at h
  linarith

/-- Every finite-basis approximation of an observable only tests finitely
many of the matrix coefficients in the weak operator convergence hypothesis. -/
theorem tracePairing_basisProjection_mul_tendsto {α ι : Type*}
    (l : Filter α) (A : α → TraceClass H) (T : TraceClass H)
    (hlim : ∀ x y : H, Tendsto (fun n => ⟪y, (A n).1 x⟫_ℂ) l (𝓝 ⟪y, T.1 x⟫_ℂ))
    (b : HilbertBasis ι ℂ H) (s : Finset ι) (K : H →L[ℂ] H) :
    Tendsto (fun n => tracePairing (A n) (basisProjection b s * K)) l
      (𝓝 (tracePairing T (basisProjection b s * K))) := by
  simp only [basisProjection_mul_eq_sum_rankOne, map_sum, tracePairing_rankOne]
  exact tendsto_finset_sum s (fun i _ => hlim (b i) (K.adjoint (b i)))

/-- Uniformly trace-norm bounded weak operator convergence implies convergence
against every compact observable, on an arbitrary complete Hilbert space.
Neither positivity nor separability is needed for this implication. -/
theorem tracePairing_compact_tendsto {α : Type*} (l : Filter α)
    (A : α → TraceClass H) (T : TraceClass H) (C : ℝ)
    (hbound : ∀ n, ‖A n‖ ≤ C)
    (hlim : ∀ x y : H, Tendsto (fun n => ⟪y, (A n).1 x⟫_ℂ) l (𝓝 ⟪y, T.1 x⟫_ℂ))
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    Tendsto (fun n => tracePairing (A n) K) l (𝓝 (tracePairing T K)) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let S : Set (H →L[ℂ] H) := Set.range (fun s : Finset w => basisProjection b s * K)
  have hclosure : K ∈ closure S :=
    mem_closure_of_tendsto (basisProjection_mul_tendsto b K hK)
      (Eventually.of_forall (fun s => Set.mem_range_self s))
  apply tendsto_functionals_at_closure_filter l (fun n => tracePairing (A n))
    (tracePairing T) (max C ‖T‖) (le_trans (norm_nonneg T) (le_max_right _ _))
    (fun n => (tracePairing_opNorm_le (A n)).trans ((hbound n).trans (le_max_left _ _)))
    ((tracePairing_opNorm_le T).trans (le_max_right _ _)) (S := S) _ hclosure
  rintro _ ⟨s, rfl⟩
  exact tracePairing_basisProjection_mul_tendsto l A T hlim b s K

/-- For positive inputs it is enough to assume an upper bound on the actual trace. -/
theorem tracePairing_compact_tendsto_of_nonneg {α : Type*} (l : Filter α)
    (A : α → TraceClass H) (T : TraceClass H) (C : ℝ)
    (hA : ∀ n, 0 ≤ (A n).1)
    (htrace : ∀ n, (traceCLM (A n)).re ≤ C)
    (hlim : ∀ x y : H, Tendsto (fun n => ⟪y, (A n).1 x⟫_ℂ) l (𝓝 ⟪y, T.1 x⟫_ℂ))
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    Tendsto (fun n => tracePairing (A n) K) l (𝓝 (tracePairing T K)) := by
  apply tracePairing_compact_tendsto l A T C _ hlim K hK
  intro n
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (hA n)]
  exact htrace n

end
end Cloning.InfiniteTraceClass
