import Cloning.InfiniteCompletelyPositiveCompactness
import Cloning.InfiniteTraceClassAsymptoticBound

/-! Compact CP limits under an independent operator-norm bound and an
asymptotic trace bound. Approximate covariance passes to the same limit. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology ComplexOrder InnerProductSpace
open Filter TopologicalSpace

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [SeparableSpace K]

/-- The uniform operator-norm bound constructs a trace-class limit; the
asymptotic positive-input trace bound gives its sharper trace estimate. -/
theorem exists_subsequence_cp_limit_of_eventual_trace_bound
    (L : ℕ → TraceClass H →L[ℂ] TraceClass K) (M c : ℝ)
    (hbound : ∀ n, ‖L n‖ ≤ M)
    (hcp : ∀ n, IsCompletelyPositive (L n).toLinearMap)
    (htrace : ∀ A, 0 ≤ A.1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (traceCLM (L n A)).re ≤ c * (traceCLM A).re + ε) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ c * (traceCLM A).re) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop
          (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K →L[ℂ] K), IsCompactOperator O →
          Tendsto (fun n => tracePairing (L (φ n) A) O) atTop
            (𝓝 (tracePairing (Ψ A) O))) := by
  have hM : 0 ≤ M := (norm_nonneg (L 0)).trans (hbound 0)
  have htraceM (n : ℕ) (A : TraceClass H) (hA : 0 ≤ A.1) :
      (traceCLM (L n A)).re ≤ M * (traceCLM A).re := by
    have hp : 0 ≤ (L n A).1 := (hcp n).map_nonneg A hA
    calc
      (traceCLM (L n A)).re = ‖L n A‖ :=
        (TraceClass.norm_eq_trace_re_of_nonneg _ hp).symm
      _ ≤ ‖L n‖ * ‖A‖ := (L n).le_opNorm A
      _ ≤ M * ‖A‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg A)
      _ = M * (traceCLM A).re := by
        rw [TraceClass.norm_eq_trace_re_of_nonneg A hA]
        rfl
  obtain ⟨Ψ, hp, _, φ, hφ, hlim, hcompact⟩ :=
    exists_subsequence_completelyPositive_limit (fun n => (L n).toLinearMap)
      M hM hcp htraceM
  refine ⟨Ψ, hp, ?_, φ, hφ, hlim, hcompact⟩
  intro A hA
  apply Cloning.InfiniteTraceClassAsymptoticBound.trace_le_of_diagonal_tendsto (l := atTop)
    (fun n => L (φ n) A) (Ψ A) (fun n => (hcp (φ n)).map_nonneg A hA)
    (hp.map_nonneg A hA) (c * (traceCLM A).re) (fun x => hlim A x x)
  intro ε hε
  exact hφ.tendsto_atTop.eventually (htrace A hA ε hε)

/-- The full common-subsequence conclusion including exact covariance, for
any parameter set, under eventual positive-input trace estimates. -/
theorem exists_subsequence_covariant_cp_limit_of_eventual_trace_bound {G : Type*}
    (L : ℕ → TraceClass H →L[ℂ] TraceClass K) (M c : ℝ)
    (hbound : ∀ n, ‖L n‖ ≤ M)
    (hcp : ∀ n, IsCompletelyPositive (L n).toLinearMap)
    (htrace : ∀ A, 0 ≤ A.1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (traceCLM (L n A)).re ≤ c * (traceCLM A).re + ε)
    (U : G → H →L[ℂ] H) (V : G → K →L[ℂ] K)
    (hdefect : ∀ g A, Tendsto (fun n =>
      ‖L n (sandwichCLM (U g) (star (U g)) A) -
        sandwichCLM (V g) (star (V g)) (L n A)‖) atTop (𝓝 (0 : ℝ))) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ c * (traceCLM A).re) ∧
      (∀ g A, Ψ (sandwichCLM (U g) (star (U g)) A) =
        sandwichCLM (V g) (star (V g)) (Ψ A)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop
          (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K →L[ℂ] K), IsCompactOperator O →
          Tendsto (fun n => tracePairing (L (φ n) A) O) atTop
            (𝓝 (tracePairing (Ψ A) O))) := by
  obtain ⟨Ψ, hp, ht, φ, hφ, hlim, hcompact⟩ :=
    exists_subsequence_cp_limit_of_eventual_trace_bound L M c hbound hcp htrace
  exact ⟨Ψ, hp, ht, covariance_of_subsequence_weakLimit
    (fun n => (L n).toLinearMap) Ψ φ hφ hlim U V hdefect, φ, hφ, hlim, hcompact⟩

omit [SeparableSpace H] [SeparableSpace K] in
private lemma eventual_trace_bound_of_limsup
    (L : ℕ → TraceClass H →L[ℂ] TraceClass K) (M c : ℝ)
    (hbound : ∀ n, ‖L n‖ ≤ M)
    (hcp : ∀ n, IsCompletelyPositive (L n).toLinearMap)
    (htrace : ∀ A, 0 ≤ A.1 →
      Filter.limsup (fun n => (traceCLM (L n A)).re) atTop ≤ c * (traceCLM A).re)
    (A : TraceClass H) (hA : 0 ≤ A.1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (traceCLM (L n A)).re ≤ c * (traceCLM A).re + ε := by
  have hb : BddAbove (Set.range (fun n => (traceCLM (L n A)).re)) := by
    refine ⟨M * ‖A‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc
      (traceCLM (L n A)).re = ‖L n A‖ :=
        (TraceClass.norm_eq_trace_re_of_nonneg _ ((hcp n).map_nonneg A hA)).symm
      _ ≤ ‖L n‖ * ‖A‖ := (L n).le_opNorm A
      _ ≤ M * ‖A‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg A)
  exact (eventually_lt_add_pos_of_limsup_le hb.isBoundedUnder_of_range
    (htrace A hA) hε).mono (fun _ h => h.le)

/-- A direct limsup formulation of the compact CP limit theorem. The sole
compactness premise is the uniform norm bound on the original maps. -/
theorem exists_subsequence_cp_limit_of_limsup_trace_bound
    (L : ℕ → TraceClass H →L[ℂ] TraceClass K) (M c : ℝ)
    (hbound : ∀ n, ‖L n‖ ≤ M)
    (hcp : ∀ n, IsCompletelyPositive (L n).toLinearMap)
    (htrace : ∀ A, 0 ≤ A.1 →
      Filter.limsup (fun n => (traceCLM (L n A)).re) atTop ≤ c * (traceCLM A).re) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ c * (traceCLM A).re) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop
          (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K →L[ℂ] K), IsCompactOperator O →
          Tendsto (fun n => tracePairing (L (φ n) A) O) atTop
            (𝓝 (tracePairing (Ψ A) O))) :=
  exists_subsequence_cp_limit_of_eventual_trace_bound L M c hbound hcp
    (eventual_trace_bound_of_limsup L M c hbound hcp htrace)

/-- Actual compact-CP-limit extraction with the manuscript's limsup trace
bound and vanishing covariance defects, for any (possibly uncountable)
parameter family. The same limit and subsequence satisfy every conclusion. -/
theorem exists_subsequence_covariant_cp_limit_of_limsup_trace_bound {G : Type*}
    (L : ℕ → TraceClass H →L[ℂ] TraceClass K) (M c : ℝ)
    (hbound : ∀ n, ‖L n‖ ≤ M)
    (hcp : ∀ n, IsCompletelyPositive (L n).toLinearMap)
    (htrace : ∀ A, 0 ≤ A.1 →
      Filter.limsup (fun n => (traceCLM (L n A)).re) atTop ≤ c * (traceCLM A).re)
    (U : G → H →L[ℂ] H) (V : G → K →L[ℂ] K)
    (hdefect : ∀ g A, Tendsto (fun n =>
      ‖L n (sandwichCLM (U g) (star (U g)) A) -
        sandwichCLM (V g) (star (V g)) (L n A)‖) atTop (𝓝 (0 : ℝ))) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ c * (traceCLM A).re) ∧
      (∀ g A, Ψ (sandwichCLM (U g) (star (U g)) A) =
        sandwichCLM (V g) (star (V g)) (Ψ A)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop
          (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K →L[ℂ] K), IsCompactOperator O →
          Tendsto (fun n => tracePairing (L (φ n) A) O) atTop
            (𝓝 (tracePairing (Ψ A) O))) :=
  exists_subsequence_covariant_cp_limit_of_eventual_trace_bound L M c hbound hcp
    (eventual_trace_bound_of_limsup L M c hbound hcp htrace) U V hdefect

end
end Cloning.InfiniteTraceClass
