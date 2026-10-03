import Cloning.InfiniteChannelCompactness
import Cloning.InfiniteChannelLimitReconstruction
import Cloning.InfiniteTraceBoundedMaps
import Cloning.InfiniteChannelTraceRepair
import Cloning.InfiniteChannelWeakLimit
import Cloning.InfiniteCompactObservableLimit
import Cloning.InfiniteChannelCovariance

/-! The compact completely-positive limit theorem for actual trace-class maps.
Complete positivity and a common positive-input trace bound imply existence of
one subsequence converging on every input and every compact output observable.
Neither a limit map, continuity, nor an extracted subsequence is a premise. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology ComplexOrder InnerProductSpace
open Filter TopologicalSpace

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [SeparableSpace K]

/-- A sequence of CP trace-class maps with a uniform positive-input trace bound
has an actual common subsequence converging to a CP map with the same bound.
The convergence holds for all inputs and all compact observables. -/
theorem exists_subsequence_completelyPositive_limit
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K) (c : ℝ) (hc : 0 ≤ c)
    (hcp : ∀ n, IsCompletelyPositive (L n))
    (htrace : ∀ n A, 0 ≤ A.1 → (traceCLM (L n A)).re ≤ c * (traceCLM A).re) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ c * (traceCLM A).re) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop
          (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K →L[ℂ] K), IsCompactOperator O →
          Tendsto (fun n => tracePairing (L (φ n) A) O) atTop
            (𝓝 (tracePairing (Ψ A) O))) := by
  have hpos (n : ℕ) := (hcp n).map_nonneg
  let U : ℕ → TraceClass H →L[ℂ] TraceClass K := fun n =>
    toContinuousLinearMapOfTraceBound (L n) (hpos n) hc (htrace n)
  have hnorm (n : ℕ) (A : TraceClass H) : ‖U n A‖ ≤ (2 * c) * ‖A‖ :=
    norm_map_le_two_mul_of_trace_bound (L n) (hpos n) hc (htrace n) A
  obtain ⟨T, φ, hφ, hlim⟩ := exists_subsequence_bounded_operator_limit U
    (2 * c) (by positivity) hnorm
  have hlim' (A : TraceClass H) (x y : K) :
      Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop (𝓝 ⟪x, T A y⟫_ℂ) :=
    hlim A x y
  obtain ⟨Ψ, hΨ⟩ := exists_linearMap_of_coefficient_limit
    (fun n => L (φ n)) T c (fun n => hpos (φ n)) (fun n => htrace (φ n)) hlim'
  have hcoeff (A : TraceClass H) (x y : K) :
      Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ) := by
    rw [hΨ]
    exact hlim' A x y
  have hcpΨ : IsCompletelyPositive Ψ := by
    intro m A hA
    apply BlockPositive.of_weakOperator_tendsto (l := atTop)
      (fun n i j => L (φ n) (A i j)) (fun i j => Ψ (A i j))
      (fun n => hcp (φ n) m A hA)
    intro i j x y
    exact hcoeff (A i j) x y
  have htraceΨ (A : TraceClass H) (hA : 0 ≤ A.1) :
      (traceCLM (Ψ A)).re ≤ c * (traceCLM A).re := by
    have hdiag (x : K) : Tendsto (fun n => ⟪(L (φ n) A).1 x, x⟫_ℂ) atTop
        (𝓝 ⟪(Ψ A).1 x, x⟫_ℂ) := by
      convert (hcoeff A x x).star using 1
      · ext n; exact (inner_conj_symm _ _).symm
      · congr 1; exact (inner_conj_symm _ _).symm
    obtain ⟨_, _, hb⟩ := InfiniteTraceClassWeakLimit.traceClass_of_diagonal_tendsto
      (fun n => (L (φ n) A).1) (Ψ A).1 (fun n => hpos (φ n) A hA)
      (fun n => (L (φ n) A).2) (c * (traceCLM A).re)
      (fun n => htrace (φ n) A hA) hdiag
    exact hb
  refine ⟨Ψ, hcpΨ, htraceΨ, φ, hφ, hcoeff, ?_⟩
  intro A O hO
  exact tracePairing_compact_tendsto atTop (fun n => L (φ n) A) (Ψ A)
    ((2 * c) * ‖A‖) (fun n => hnorm (φ n) A) (fun x y => hcoeff A y x) O hO

/-- Approximate covariance for an arbitrary parameter family becomes exact
for the same extracted CP limit. The parameter set need not be countable. -/
theorem exists_subsequence_covariant_completelyPositive_limit {G : Type*}
    (L : ℕ → TraceClass H →ₗ[ℂ] TraceClass K) (c : ℝ) (hc : 0 ≤ c)
    (hcp : ∀ n, IsCompletelyPositive (L n))
    (htrace : ∀ n A, 0 ≤ A.1 → (traceCLM (L n A)).re ≤ c * (traceCLM A).re)
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
    exists_subsequence_completelyPositive_limit L c hc hcp htrace
  exact ⟨Ψ, hp, ht, covariance_of_subsequence_weakLimit L Ψ φ hφ hlim U V hdefect,
    φ, hφ, hlim, hcompact⟩

/-- In particular, actual quantum channels admit a CP trace-nonincreasing
subsequential limit. Escaping trace is permitted and is not silently restored. -/
theorem exists_subsequence_quantumChannel_limit (Φ : ℕ → QuantumChannel H K) :
    ∃ Ψ : TraceClass H →ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ (traceCLM A).re) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n => ⟪x, ((Φ (φ n)).toLinearMap A).1 y⟫_ℂ) atTop
          (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K →L[ℂ] K), IsCompactOperator O →
          Tendsto (fun n => tracePairing ((Φ (φ n)).toLinearMap A) O) atTop
            (𝓝 (tracePairing (Ψ A) O))) := by
  have ht (n : ℕ) (A : TraceClass H) (_hA : 0 ≤ A.1) :
      (traceCLM ((Φ n).toLinearMap A)).re ≤ 1 * (traceCLM A).re := by
    simpa using le_of_eq (congrArg Complex.re ((Φ n).trace_preserving A))
  simpa only [one_mul] using exists_subsequence_completelyPositive_limit
    (fun n => (Φ n).toLinearMap) 1 zero_le_one (fun n => (Φ n).completelyPositive) ht

end
end Cloning.InfiniteTraceClass
