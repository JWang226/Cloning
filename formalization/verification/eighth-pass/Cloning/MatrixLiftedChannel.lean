import Cloning.Channels
import Cloning.MatrixFidelityBlocks
import Cloning.MatrixFidelityTensor
import Cloning.MatrixFidelityLifted

/-!
# Concrete finite sector transitions and ancillary lifting

An arbitrary finite family of actual matrix channels, positive input states,
and nonnegative joint sector weights determines positive output blocks.
Appending normalized ancillary states and taking a dependent orthogonal direct
sum gives an actual density matrix. The Schur and PRV identifications are not
assumed or asserted here.
-/

noncomputable section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix
open Cloning.Channels Cloning.MatrixFidelity

namespace Cloning.MatrixLiftedChannel

set_option backward.isDefEq.respectTransparency false

/-- Positivity follows from the concrete definition of complete positivity,
by amplification with a one-dimensional ancilla. -/
theorem map_positive {α β : Type*} [Fintype α] [Fintype β]
    (Φ : MatrixChannel α β) {X : Matrix α α ℂ} (hX : X.PosSemidef) :
    (Φ.toFun X).PosSemidef := by
  have hcp := Φ.completely_positive 1 ((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ X)
    (Matrix.PosSemidef.one.kronecker hX)
  have hres := hcp.submatrix (fun i : β => ((0 : Fin 1), i))
  simpa [Channels.amplify, Matrix.submatrix, Matrix.kroneckerMap_apply] using hres

variable {μ ν : Type*} [Fintype μ]
variable {α : μ → Type*} {β : ν → Type*}
variable [∀ i, Fintype (α i)] [∀ j, Fintype (β j)]

/-- Unnormalized output block for a fixed output sector. -/
def transitionOutput (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (joint : μ → ν → ℝ) (j : ν) : Matrix (β j) (β j) ℂ :=
  ∑ i, joint i j • (Φ i j).toFun (ρ i).matrix

theorem transitionOutput_posSemidef (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) {joint : μ → ν → ℝ}
    (hjoint : ∀ i j, 0 ≤ joint i j) (j : ν) :
    (transitionOutput Φ ρ joint j).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (map_positive (Φ i j) (ρ i).positive).smul (hjoint i j)

/-- The mass of an output block is exactly the output marginal weight. -/
theorem transitionOutput_trace (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (joint : μ → ν → ℝ) (j : ν) :
    Matrix.trace (transitionOutput Φ ρ joint j) = ((∑ i, joint i j : ℝ) : ℂ) := by
  simp [transitionOutput, Matrix.trace_sum, MatrixChannel.trace_preserving, State.trace_one]

theorem transitionOutput_trace_re (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (joint : μ → ν → ℝ) (j : ν) :
    (Matrix.trace (transitionOutput Φ ρ joint j)).re = ∑ i, joint i j := by
  rw [transitionOutput_trace]
  rfl

variable [Fintype ν] [DecidableEq ν]
variable {κ : ν → Type*} [∀ j, Fintype (κ j)]
variable [∀ j, DecidableEq (β j)] [∀ j, DecidableEq (κ j)]

/-- Joint law obtained by measuring an input sector and sampling an output
sector through a classical transition kernel. -/
def kernelJoint (p : μ → ℝ) (K : μ → ν → ℝ) (i : μ) (j : ν) : ℝ :=
  p i * K i j

omit [Fintype μ] [Fintype ν] [DecidableEq ν] in
theorem kernelJoint_nonneg {p : μ → ℝ} {K : μ → ν → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hK : ∀ i j, 0 ≤ K i j) :
    ∀ i j, 0 ≤ kernelJoint p K i j :=
  fun i j => mul_nonneg (hp i) (hK i j)

omit [DecidableEq ν] in
/-- A probability law followed by a stochastic kernel has total mass one. -/
theorem kernelJoint_mass {p : μ → ℝ} {K : μ → ν → ℝ}
    (hp : ∑ i, p i = 1) (hK : ∀ i, ∑ j, K i j = 1) :
    ∑ j, ∑ i, kernelJoint p K i j = 1 := by
  unfold kernelJoint
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]
  exact hp

/-- Orthogonal output sectors with a normalized ancilla in each sector. -/
def liftedOutput (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (τ : ∀ j, State (κ j)) (joint : μ → ν → ℝ) :
    Matrix (Σ j, β j × κ j) (Σ j, β j × κ j) ℂ :=
  Matrix.blockDiagonal' (fun j => transitionOutput Φ ρ joint j ⊗ₖ (τ j).matrix)

theorem liftedOutput_posSemidef (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (τ : ∀ j, State (κ j)) {joint : μ → ν → ℝ}
    (hjoint : ∀ i j, 0 ≤ joint i j) : (liftedOutput Φ ρ τ joint).PosSemidef := by
  apply blockDiagonal'_posSemidef
  intro j
  exact (transitionOutput_posSemidef Φ ρ hjoint j).kronecker (τ j).positive

omit [∀ j, DecidableEq (κ j)] [∀ j, DecidableEq (β j)] in
theorem liftedOutput_trace (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (τ : ∀ j, State (κ j)) (joint : μ → ν → ℝ) :
    Matrix.trace (liftedOutput Φ ρ τ joint) = ((∑ j, ∑ i, joint i j : ℝ) : ℂ) := by
  simp [liftedOutput, Matrix.trace_blockDiagonal', Matrix.trace_kronecker,
    State.trace_one, transitionOutput_trace]

/-- The complete finite transition construction yields a density matrix. -/
def liftedState (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (τ : ∀ j, State (κ j)) (joint : μ → ν → ℝ)
    (hjoint : ∀ i j, 0 ≤ joint i j) (hmass : ∑ j, ∑ i, joint i j = 1) :
    State (Σ j, β j × κ j) where
  matrix := liftedOutput Φ ρ τ joint
  positive := liftedOutput_posSemidef Φ ρ τ hjoint
  trace_one := by rw [liftedOutput_trace, hmass]; rfl

/-- The manuscript's finite transition rule, realized as a density matrix:
sample the input sector with law `p`, the output sector with kernel `K`, apply
its matrix channel, append the prescribed ancilla, and take the direct sum. -/
def liftedStateOfKernel (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (τ : ∀ j, State (κ j))
    (p : μ → ℝ) (K : μ → ν → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hK : ∀ i j, 0 ≤ K i j) (hKsum : ∀ i, ∑ j, K i j = 1) :
    State (Σ j, β j × κ j) :=
  liftedState Φ ρ τ (kernelJoint p K) (kernelJoint_nonneg hp hK)
    (kernelJoint_mass hpsum hKsum)

/-- Exact fidelity of the concrete transition output with a weighted target
family, using the same ancillary state in every matching sector. -/
theorem liftedOutput_fidelity (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (σ : ∀ j, State (β j)) (τ : ∀ j, State (κ j))
    {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (p : ν → ℝ) (hp : ∀ j, 0 ≤ p j) :
    fidelity (liftedOutput Φ ρ τ joint)
      (Matrix.blockDiagonal' (fun j => (p j • (σ j).matrix) ⊗ₖ (τ j).matrix)) =
      ∑ j, Real.sqrt (p j) * fidelity (transitionOutput Φ ρ joint j) (σ j).matrix := by
  exact fidelity_lifted_blocks (transitionOutput Φ ρ joint) (fun j => (σ j).matrix)
    (fun j => (τ j).matrix) p (transitionOutput_posSemidef Φ ρ hjoint)
    (fun j => (σ j).positive) (fun j => (τ j).positive) hp
    (fun j => by rw [(τ j).trace_one]; rfl)

end Cloning.MatrixLiftedChannel
