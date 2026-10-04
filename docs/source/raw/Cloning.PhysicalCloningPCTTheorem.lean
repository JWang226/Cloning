import Cloning.PCTPhysicalFidelityUnconditional

/-! The physical PCT limit with its purification dimension constructed from
the input dimension. The input is an arbitrary positive density matrix with
simple spectrum; no eigenbasis or asymptotic approximation is supplied. -/
noncomputable section
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Filter
namespace Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false

/-- The canonical number of tangent coordinates in a purification register. -/
theorem purification_register_card (k : ℕ) :
    Fintype.card (Fin (k+1) × Fin (k+1)) = k*(k+2)+1 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- The existing physical, state-independent PCT channel, with the auxiliary
purification cardinality selected internally. -/
def physicalPCTOutput {k : ℕ} (ρ : Cloning.MatrixFidelity.State (Fin (k+1)))
    (n r : ℕ) : Cloning.Hybrid.PositiveTraceClass
      (Cloning.PCT.Register (Fin (n+r) → Fin (k+1))) :=
  outputState (purification_register_card k) ρ n r

/-- Exact root fidelity of the physical PCT channel in every dimension at
least two, at an arbitrary full-rank density matrix with distinct eigenvalues. -/
theorem physical_pct_fidelity {k : ℕ} (hk : 1 ≤ k)
    (ρ : Cloning.MatrixFidelity.State (Fin (k+1))) (hpos : ρ.matrix.PosDef)
    (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (physicalPCTOutput ρ n (r n)).rootFidelity
      (tensorState ρ (n+r n))) atTop
      (𝓝 (pctValue γ (densitySpectrum ρ hpos hsimple))) := by
  have hs : 1 ≤ k*(k+2) := by nlinarith
  exact Cloning.PCTPhysicalFidelity.physical_pct_fidelity_simple_density
    ρ hpos hsimple hs (purification_register_card k) r γ hγ hr

end Cloning.PCTPhysicalState
