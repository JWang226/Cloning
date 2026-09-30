import Cloning.InfiniteTraceClassCompactness
import Cloning.InfiniteCompactObservableLimit

/-! Actual subsequence extraction with simultaneous convergence against every
compact observable. The extraction and approximation arguments are proved in
the imported modules, not supplied as hypotheses. -/

namespace Cloning.InfiniteTraceClass

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual extraction yields simultaneous convergence against every compact
observable, in addition to convergence of every matrix coefficient. -/
theorem exists_subsequence_compact_observable_limit [TopologicalSpace.SeparableSpace H]
    (A : ℕ → TraceClass H) (hA : ∀ n, 0 ≤ (A n).1) (C : ℝ)
    (htrace : ∀ n, (traceCLM (A n)).re ≤ C) :
    ∃ T : TraceClass H, 0 ≤ T.1 ∧ (traceCLM T).re ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ x y : H, Tendsto (fun n => ⟪y, (A (φ n)).1 x⟫_ℂ) atTop
          (𝓝 ⟪y, T.1 x⟫_ℂ)) ∧
        ∀ K : H →L[ℂ] H, IsCompactOperator K →
          Tendsto (fun n => tracePairing (A (φ n)) K) atTop (𝓝 (tracePairing T K)) := by
  obtain ⟨T, hT, hTC, φ, hφ, hlim⟩ :=
    exists_subsequence_weak_operator_limit A hA C htrace
  refine ⟨T, hT, hTC, φ, hφ, hlim, ?_⟩
  intro K hK
  exact tracePairing_compact_tendsto_of_nonneg atTop (fun n => A (φ n)) T C
    (fun n => hA (φ n)) (fun n => htrace (φ n)) hlim K hK

end
end Cloning.InfiniteTraceClass
