import Cloning.WeylQuantumPositiveBlocks

/-! Complete positivity passes from an actual trace-class map to its
constructed normal Heisenberg dual. Combined with the Weyl Gram calculation,
this proves the quantum-positive multiplier condition directly for physical
channels, with no complete-positivity premise on an assumed dual map. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators

namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι]

/-- The full entangled rank-one block used to test the dual amplification. -/
theorem rankOne_blockPositive (x : ι → H) :
    BlockPositive (fun i j => rankOneOperator (x i) (x j)) := by
  intro y
  have h := Cloning.BoundedOperator.gram_blockPositive (fun i => innerSL ℂ (x i)) y
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ⟪y i, ⟪x j, y j⟫_ℂ • x i⟫_ℂ =
    ⟪y i, (innerSL ℂ (x i)).adjoint (innerSL ℂ (x j) (y j))⟫_ℂ
  rw [ContinuousLinearMap.adjoint_innerSL_apply]
  rfl

/-- Complete positivity of the actual reconstructed normal Heisenberg map. -/
theorem heisenbergDual_completelyPositive
    (Φ : TraceClass H →L[ℂ] TraceClass K)
    (hΦ : IsCompletelyPositive Φ.toLinearMap) :
    Cloning.BoundedOperator.IsCompletelyPositive (heisenbergDual Φ) := by
  intro n A hA x
  have hB := hΦ n _ (rankOne_blockPositive x)
  have h := block_tracePairing_nonneg _ hB A hA
  simpa only [heisenbergDual_inner] using h

end Cloning.InfiniteTraceClass

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass

variable {d : ℕ}

/-- For a completely positive trace-class map, covariance of its actual
Heisenberg dual forces the quantum-positive scalar Weyl multiplier. -/
theorem traceClass_covariant_multiplier_isQuantumPositive
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d))
    (hΦ : IsCompletelyPositive Φ.toLinearMap) (r : ℝ)
    (hcov : ∀ (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d),
      ((displacement a).comp (heisenbergDual Φ A)).comp (displacement (-a)) =
        heisenbergDual Φ (((displacement (r • a)).comp A).comp (displacement (-(r • a))))) :
    IsQuantumPositive (weylMultiplier (heisenbergDual Φ) r) r :=
  covariant_weylMultiplier_isQuantumPositive (heisenbergDual Φ)
    (heisenbergDual_completelyPositive Φ hΦ) r hcov

end Cloning.MultimodeCoherent
