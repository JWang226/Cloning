import Cloning.WeylFoelner
import Cloning.InfiniteCompletelyPositiveCompactness

/-! An actual common subsequential, covariant CP limit of the explicit
Gaussian Følner averages. Escaping trace is allowed and remains explicit. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter TopologicalSpace

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Separability of the actual multimode Fock space follows from its continuous
coherent parametrization and the proved density of coherent superpositions. -/
instance fock_separableSpace (d : ℕ) : SeparableSpace (Fock d) := by
  apply (dense_coherentVector_span d).isSeparable_iff.mp
  exact (isSeparable_range (continuous_coherentVector d)).span


/-- Every quantum competitor has an explicitly averaged sequence with one
common subsequence converging, on all inputs and all compact observables, to
a displacement-covariant CP trace-nonincreasing map. The limit, subsequence,
and covariance are conclusions, with no compactness or regularity premise. -/
theorem exists_gaussianFoelner_covariant_limit (gain : ℝ)
    (Φ : QuantumChannel (Fock d) (Fock d)) :
    ∃ Ψ : TraceClass (Fock d) →ₗ[ℂ] TraceClass (Fock d),
      IsCompletelyPositive Ψ ∧
      (∀ A, 0 ≤ A.1 → (traceCLM (Ψ A)).re ≤ (traceCLM A).re) ∧
      (∀ (b : Fin d → ℂ) A,
        Ψ (displacementTraceMap b A) = displacementTraceMap (gain • b) (Ψ A)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ A x y, Tendsto (fun n =>
          ⟪x, ((gaussianFoelnerChannel gain Φ (φ n)).toLinearMap A).1 y⟫_ℂ) atTop
            (𝓝 ⟪x, (Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : (Fock d) →L[ℂ] (Fock d)), IsCompactOperator O →
          Tendsto (fun n => tracePairing
            ((gaussianFoelnerChannel gain Φ (φ n)).toLinearMap A) O) atTop
              (𝓝 (tracePairing (Ψ A) O))) := by
  let L := fun n => (gaussianFoelnerChannel gain Φ n).toLinearMap
  have ht (n : ℕ) (A : TraceClass (Fock d)) (_hA : 0 ≤ A.1) :
      (traceCLM (L n A)).re ≤ 1 * (traceCLM A).re := by
    simpa only [one_mul] using
      le_of_eq (congrArg Complex.re ((gaussianFoelnerChannel gain Φ n).trace_preserving A))
  have hd (b : Fin d → ℂ) (A : TraceClass (Fock d)) :
      Tendsto (fun n =>
        ‖L n (sandwichCLM (displacement b) (star (displacement b)) A) -
          sandwichCLM (displacement (gain • b)) (star (displacement (gain • b)))
            (L n A)‖) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
      displacementTraceMap] using gaussianFoelnerChannel_covariance_tendsto_all gain Φ b A
  have h := exists_subsequence_covariant_completelyPositive_limit L 1 zero_le_one
    (fun n => (gaussianFoelnerChannel gain Φ n).completelyPositive) ht
    displacement (fun b => displacement (gain • b)) hd
  simpa only [one_mul, ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
    displacementTraceMap] using h

end Cloning.MultimodeCoherent
