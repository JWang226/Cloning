import Cloning.MatrixLiftedCPTPKraus

/-! The sector instrument on the actual physical trace-class registers. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix Cloning.Channels Cloning.MatrixFidelity Cloning.MatrixLiftedChannel
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel

namespace Cloning.MatrixLiftedCPTP

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
variable {α χ : μ → Type*} {β κ : ν → Type*}
variable [∀ i, Fintype (α i)] [∀ i, Fintype (χ i)]
variable [∀ j, Fintype (β j)] [∀ j, Fintype (κ j)]
variable [∀ i, DecidableEq (α i)] [∀ i, DecidableEq (χ i)]
variable [∀ j, DecidableEq (β j)] [∀ j, DecidableEq (κ j)]

/-- The complete sector instrument on the physical trace-class spaces.
Its CP and TP laws hold on all inputs, including coherent cross-sector inputs. -/
def physicalChannel (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j)) :
    QuantumChannel (Register (Σ i, α i × χ i)) (Register (Σ j, β j × κ j)) :=
  registerChannel (channel Φ K hK hKsum τ)

theorem physicalChannel_matrix (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    (physicalChannel Φ K hK hKsum τ).toLinearMap (registerLiftCLM X) =
      registerLiftCLM (channelMap Φ K τ X) :=
  registerChannel_matrix (channel Φ K hK hKsum τ) X

/-- The physical channel produces exactly the desired lifted output law,
independently of every discarded input multiplicity state. -/
theorem physicalChannel_weightedInput (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (ρ : ∀ i, State (α i)) (σ : ∀ i, State (χ i)) (p : μ → ℝ) :
    (physicalChannel Φ K hK hKsum τ).toLinearMap
      (registerLiftCLM (Matrix.blockDiagonal'
        (fun i => (p i • (ρ i).matrix) ⊗ₖ (σ i).matrix))) =
      registerLiftCLM (liftedOutput Φ ρ τ (kernelJoint p K)) := by
  rw [physicalChannel, registerChannel_matrix, channel_weightedInput]

/-- For a probability input law, the physical output is exactly the previously
defined output density matrix, now obtained from a genuine channel. -/
theorem physicalChannel_liftedStateOfKernel (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (ρ : ∀ i, State (α i)) (σ : ∀ i, State (χ i)) (p : μ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    (physicalChannel Φ K hK hKsum τ).toLinearMap
      (registerLiftCLM (Matrix.blockDiagonal'
        (fun i => (p i • (ρ i).matrix) ⊗ₖ (σ i).matrix))) =
      registerLiftCLM (liftedStateOfKernel Φ ρ τ p K hp hpsum hK hKsum).matrix :=
  physicalChannel_weightedInput Φ K hK hKsum τ ρ σ p

end Cloning.MatrixLiftedCPTP
