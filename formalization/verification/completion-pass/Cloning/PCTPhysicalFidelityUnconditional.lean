import Cloning.PCTPhysicalStateSpectrum
import Cloning.TensorLANEmbeddingCompactLAN

/-! The actual state-independent global PCT channel has the stated physical
fidelity limit. The compact-window mixed LAN theorem is constructed, and no
Gaussian approximation, chart, frame, or LAN premise remains. -/
noncomputable section
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Filter
namespace Cloning.PCTPhysicalFidelity
open Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.PCTJointGaussianWhitening Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
variable {k s : ℕ}

/-- Unconditional physical PCT root-fidelity limit on every unitary orbit of
a positive simple spectrum. -/
theorem physical_pct_fidelity_unitary
    (p : SimpleSpectrum (k+1)) (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ))
    (hs : 1 ≤ s) (hcard : Fintype.card (Fin (k+1) × Fin (k+1)) = s+1)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n =>
      (outputState hcard (conjugatedState (baseState p) U) n (r n)).rootFidelity
      (tensorState (conjugatedState (baseState p) U) (n+r n))) atTop (𝓝 (pctValue γ p)) := by
  obtain ⟨b,hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (k+1)) = k+1)
    p.eigenvalue (fun a => (p.positive a).le) p.normalized
  let e := (Fintype.equivFin (PairIndex (k+1))).symm
  exact physical_pct_fidelity_unitary_of_compactWindowLAN p b hb e
    (physicalCompactWindowLAN p b hb e) U hs hcard r γ hγ hr

/-- An arbitrary full-rank density matrix with distinct eigenvalues needs no
supplied diagonalization: its spectrum and unitary are constructed. -/
theorem physical_pct_fidelity_simple_density
    (ρ : Cloning.MatrixFidelity.State (Fin (k+1))) (hpos : ρ.matrix.PosDef)
    (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues)
    (hs : 1 ≤ s) (hcard : Fintype.card (Fin (k+1) × Fin (k+1)) = s+1)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (outputState hcard ρ n (r n)).rootFidelity
      (tensorState ρ (n+r n))) atTop (𝓝 (pctValue γ (densitySpectrum ρ hpos hsimple))) := by
  let p := densitySpectrum ρ hpos hsimple
  obtain ⟨b,hb⟩ := exists_whitening_frame (by simp : Fintype.card (Fin (k+1)) = k+1)
    p.eigenvalue (fun a => (p.positive a).le) p.normalized
  let e := (Fintype.equivFin (PairIndex (k+1))).symm
  exact physical_pct_fidelity_of_simple_density ρ hpos hsimple b hb e
    (physicalCompactWindowLAN p b hb e) hs hcard r γ hγ hr

end Cloning.PCTPhysicalFidelity
