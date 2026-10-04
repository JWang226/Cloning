import Cloning.MatrixLiftedCPTP
import Cloning.MatrixChannelFidelity

/-! Exact action of the genuine sector channel on the manuscript's lifted states. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix Cloning.Channels Cloning.MatrixFidelity Cloning.MatrixLiftedChannel

namespace Cloning.MatrixLiftedCPTP

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
variable {α χ : μ → Type*} {β κ : ν → Type*}
variable [∀ i, Fintype (α i)] [∀ i, Fintype (χ i)]
variable [∀ j, Fintype (β j)] [∀ j, Fintype (κ j)]
variable [∀ i, DecidableEq (α i)] [∀ i, DecidableEq (χ i)]
variable [∀ j, DecidableEq (β j)] [∀ j, DecidableEq (κ j)]

/-- Discarding any normalized multiplicity state recovers its entire complex
sector matrix, with no positivity or trace-one requirement on that matrix. -/
theorem inputReduction_blockDiagonal (Y : ∀ i, Matrix (α i) (α i) ℂ)
    (σ : ∀ i, State (χ i)) (i : μ) :
    inputReduction i (Matrix.blockDiagonal' (fun i => Y i ⊗ₖ (σ i).matrix)) = Y i := by
  ext a b
  simp only [inputReduction, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  rw [← Finset.mul_sum]
  change Y i a b * Matrix.trace (σ i).matrix = Y i a b
  rw [(σ i).trace_one, mul_one]

/-- The output law of the actual channel agrees with the previously defined
transition blocks, independently of the discarded multiplicity states. -/
theorem outputBlock_weightedInput (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (ρ : ∀ i, State (α i)) (σ : ∀ i, State (χ i))
    (p : μ → ℝ) (j : ν) :
    outputBlock Φ K j
      (Matrix.blockDiagonal' (fun i => (p i • (ρ i).matrix) ⊗ₖ (σ i).matrix)) =
      transitionOutput Φ ρ (kernelJoint p K) j := by
  simp only [outputBlock, inputReduction_blockDiagonal,
    channel_map_real_smul, smul_smul, transitionOutput, kernelJoint]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The all-input CPTP construction has exactly the desired lifted output. -/
theorem channel_weightedInput (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (ρ : ∀ i, State (α i)) (σ : ∀ i, State (χ i)) (p : μ → ℝ) :
    (channel Φ K hK hKsum τ).toFun
      (Matrix.blockDiagonal' (fun i => (p i • (ρ i).matrix) ⊗ₖ (σ i).matrix)) =
      liftedOutput Φ ρ τ (kernelJoint p K) := by
  simp only [channel, channelMap, outputBlock_weightedInput, liftedOutput]

/-- In particular, a probability law gives exactly `liftedStateOfKernel`,
now as the action of one genuine CPTP map on all input states. -/
theorem channel_liftedStateOfKernel (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (ρ : ∀ i, State (α i)) (σ : ∀ i, State (χ i)) (p : μ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    (channel Φ K hK hKsum τ).toFun
      (Matrix.blockDiagonal' (fun i => (p i • (ρ i).matrix) ⊗ₖ (σ i).matrix)) =
      (liftedStateOfKernel Φ ρ τ p K hp hpsum hK hKsum).matrix :=
  channel_weightedInput Φ K hK hKsum τ ρ σ p

/-- Fidelity of the actual channel output, including its prepared ancillary
states, equals the previously established exact sector formula. -/
theorem channel_weightedInput_fidelity (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (ρ : ∀ i, State (α i)) (σ : ∀ i, State (χ i))
    (p : μ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (target : ∀ j, State (β j)) (q : ν → ℝ) (hq : ∀ j, 0 ≤ q j) :
    fidelity ((channel Φ K hK hKsum τ).toFun
      (Matrix.blockDiagonal' (fun i => (p i • (ρ i).matrix) ⊗ₖ (σ i).matrix)))
      (Matrix.blockDiagonal' (fun j => (q j • (target j).matrix) ⊗ₖ (τ j).matrix)) =
      ∑ j, Real.sqrt (q j) *
        fidelity (transitionOutput Φ ρ (kernelJoint p K) j) (target j).matrix := by
  rw [channel_weightedInput]
  exact liftedOutput_fidelity Φ ρ target τ (kernelJoint_nonneg hp hK) q hq

end Cloning.MatrixLiftedCPTP
