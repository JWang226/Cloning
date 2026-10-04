import Cloning.MatrixChannelFidelity
import Cloning.MatrixChannelTraceNorm
import Cloning.MatrixFidelityContinuity
import Cloning.MatrixLiftedChannel
import Cloning.LAN

/-!
# Approximation transfer for actual finite-dimensional quantum experiments

All channel positivity, data processing, trace-norm contraction, and fidelity
continuity used here are proved for actual complex matrices in the imported
modules. Only the quantitative approximation errors remain hypotheses.

The comparison experiments here are finite-dimensional. This does not
construct the infinite-dimensional Gaussian LAN channels of the manuscript.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Topology
open Matrix Filter MeasureTheory
open Cloning.Channels Cloning.MatrixFidelity Cloning.MatrixLiftedChannel

namespace Cloning.MatrixLANTransfer

set_option backward.isDefEq.respectTransparency false

variable {a b g h : Type*} [Fintype a] [Fintype b] [Fintype g] [Fintype h]

/-- Actual matrix channels are closed under composition. -/
def compose (T : MatrixChannel b h) (M : MatrixChannel a b) : MatrixChannel a h where
  toFun := fun X => T.toFun (M.toFun X)
  map_add := by intro X Y; rw [M.map_add, T.map_add]
  map_smul := by intro c X; rw [M.map_smul, T.map_smul]
  trace_preserving := by intro X; rw [T.trace_preserving, M.trace_preserving]
  completely_positive := by
    intro k X hX
    change (amplify T.toFun (amplify M.toFun X)).PosSemidef
    exact T.completely_positive k _ (M.completely_positive k X hX)

/-- The image of a density matrix under an actual matrix channel. -/
def mapState (M : MatrixChannel a b) (ρ : State a) : State b where
  matrix := M.toFun ρ.matrix
  positive := map_positive M ρ.positive
  trace_one := by rw [M.trace_preserving, ρ.trace_one]

variable [DecidableEq a] [DecidableEq b] [DecidableEq g] [DecidableEq h]

/-- Swapping the arguments of the trace-norm error does not change it. -/
theorem traceNorm_sub_symm (A B : Matrix a a ℂ) :
    matrixTraceNorm (A - B) = matrixTraceNorm (B - A) := by
  have hneg : ∀ X : Matrix a a ℂ, matrixTraceNorm (-X) = matrixTraceNorm X := by
    intro X
    simp [matrixTraceNorm]
  rw [← neg_sub B A, hneg]

omit [DecidableEq g] in
/-- The matrix version of the manuscript's channel-composition transfer
estimate. No contractivity, data-processing, or continuity laws are assumed. -/
theorem fidelity_transfer
    (S : MatrixChannel g a) (M : MatrixChannel a b) (T : MatrixChannel b h)
    (ρ : State a) (σ : State b) (Φ : State g) (Ψ : State h) {δ η : ℝ}
    (hδ : matrixTraceNorm (S.toFun Φ.matrix - ρ.matrix) ≤ δ)
    (hη : matrixTraceNorm (T.toFun σ.matrix - Ψ.matrix) ≤ η) :
    fidelity (M.toFun ρ.matrix) σ.matrix ≤
      fidelity (T.toFun (M.toFun (S.toFun Φ.matrix))) Ψ.matrix +
        Real.sqrt δ + Real.sqrt η := by
  have hSΦ := map_positive S Φ.positive
  have hMρ := map_positive M ρ.positive
  have hMSΦ := map_positive M hSΦ
  have hTMρ := map_positive T hMρ
  have hTMSΦ := map_positive T hMSΦ
  have hTσ := map_positive T σ.positive
  have hδ' : matrixTraceNorm (ρ.matrix - S.toFun Φ.matrix) ≤ δ := by
    rwa [traceNorm_sub_symm]
  have herror : matrixTraceNorm
      (T.toFun (M.toFun ρ.matrix) - T.toFun (M.toFun (S.toFun Φ.matrix))) ≤ δ :=
    (T.traceNorm_contract_sub hMρ hMSΦ).trans
      ((M.traceNorm_contract_sub ρ.positive hSΦ).trans hδ')
  have hcont := fidelity_continuity_of_traceNorm_le hTMρ hTMSΦ hTσ Ψ.positive
    (by rw [T.trace_preserving, σ.trace_one]; norm_num)
    (by rw [T.trace_preserving, M.trace_preserving, S.trace_preserving, Φ.trace_one]; norm_num)
    herror hη
  have hdata := fidelity_data_processing T hMρ σ.positive
  have hle := (le_abs_self
    (fidelity (T.toFun (M.toFun ρ.matrix)) (T.toFun σ.matrix) -
      fidelity (T.toFun (M.toFun (S.toFun Φ.matrix))) Ψ.matrix)).trans hcont
  linarith

omit [DecidableEq g] in
/-- Uniform comparison of finite matrix experiments gives the actual minimax
versus Bayes bound. The only analytic premise beyond approximation is
integrability of the comparison payoff under the chosen probability prior. -/
theorem minimax_le_bayesValue
    {I P Θ : Type*} [Nonempty I] [MeasurableSpace Θ]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (S : MatrixChannel g a) (M : I → MatrixChannel a b) (T : MatrixChannel b h)
    (ρ : P → State a) (σ : P → State b) (Φ : Θ → State g) (Ψ : Θ → State h)
    (localChart : Θ → P) (δ η : ℝ)
    (hδ : ∀ θ, matrixTraceNorm (S.toFun (Φ θ).matrix - (ρ (localChart θ)).matrix) ≤ δ)
    (hη : ∀ θ, matrixTraceNorm (T.toFun (σ (localChart θ)).matrix - (Ψ θ).matrix) ≤ η)
    (hintegrable : ∀ N : MatrixChannel g h,
      Integrable (fun θ => fidelity (N.toFun (Φ θ).matrix) (Ψ θ).matrix) prior) :
    Cloning.LAN.minimaxValue
      (fun i p => fidelity ((M i).toFun (ρ p).matrix) (σ p).matrix) ≤
      Cloning.LAN.bayesValue prior
        (fun (N : MatrixChannel g h) θ => fidelity (N.toFun (Φ θ).matrix) (Ψ θ).matrix) +
          (Real.sqrt δ + Real.sqrt η) := by
  apply Cloning.LAN.minimax_le_bayesValue prior _ _ localChart
    (fun i => compose T (compose (M i) S)) _
    (fun _ _ => fidelity_nonneg _ _)
  · intro i θ
    simpa only [compose, add_assoc] using fidelity_transfer S (M i) T
      (ρ (localChart θ)) (σ (localChart θ)) (Φ θ) (Ψ θ) (hδ θ) (hη θ)
  · exact hintegrable
  · intro N θ
    exact fidelity_le_one (map_positive N (Φ θ).positive) (Ψ θ).positive
      (by rw [N.trace_preserving, (Φ θ).trace_one]; norm_num)
      (by rw [(Ψ θ).trace_one]; norm_num)

end Cloning.MatrixLANTransfer
