import Cloning.MatrixLiftedChannel
import Cloning.MatrixFidelityDeletion
import Cloning.MatrixFidelityAsymptotics

/-!
# Removing individual sector transitions from actual matrix outputs

The mask acts on pairs of input and output sectors. Contributions with the
same output sector may overlap: positivity of the discarded sum, rather than
orthogonality of its summands, proves the needed matrix domination.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix
open Cloning.Channels Cloning.MatrixFidelity Cloning.MatrixLiftedChannel

namespace Cloning.MatrixLiftedTrimming

set_option backward.isDefEq.respectTransparency false

variable {μ ν : Type*}

/-- Retained joint weights for a predicate on input/output sector pairs. -/
def keptJoint (joint : μ → ν → ℝ) (keep : μ → ν → Prop) (i : μ) (j : ν) : ℝ := by
  classical
  exact if keep i j then joint i j else 0

/-- Discarded joint weights for the same predicate. -/
def discardedJoint (joint : μ → ν → ℝ) (keep : μ → ν → Prop) (i : μ) (j : ν) : ℝ := by
  classical
  exact if keep i j then 0 else joint i j

theorem keptJoint_nonneg {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) : ∀ i j, 0 ≤ keptJoint joint keep i j := by
  classical
  intro i j
  by_cases h : keep i j <;> simp [keptJoint, h, hjoint i j]

theorem discardedJoint_nonneg {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) : ∀ i j, 0 ≤ discardedJoint joint keep i j := by
  classical
  intro i j
  by_cases h : keep i j <;> simp [discardedJoint, h, hjoint i j]

theorem keptJoint_le {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) (i : μ) (j : ν) : keptJoint joint keep i j ≤ joint i j := by
  classical
  by_cases h : keep i j <;> simp [keptJoint, h, hjoint i j]

theorem joint_sub_kept (joint : μ → ν → ℝ) (keep : μ → ν → Prop) (i : μ) (j : ν) :
    joint i j - keptJoint joint keep i j = discardedJoint joint keep i j := by
  classical
  by_cases h : keep i j <;> simp [keptJoint, discardedJoint, h]

variable [Fintype μ]
variable {α : μ → Type*} {β : ν → Type*}
variable [∀ i, Fintype (α i)] [∀ j, Fintype (β j)]

/-- The difference of full and retained outputs is exactly the discarded
positive sum, even if distinct transitions share one output sector. -/
theorem transitionOutput_sub_kept
    (Φ : ∀ i j, MatrixChannel (α i) (β j)) (ρ : ∀ i, State (α i))
    (joint : μ → ν → ℝ) (keep : μ → ν → Prop) (j : ν) :
    transitionOutput Φ ρ joint j - transitionOutput Φ ρ (keptJoint joint keep) j =
      transitionOutput Φ ρ (discardedJoint joint keep) j := by
  unfold transitionOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_smul, joint_sub_kept]

theorem transitionOutput_sub_kept_posSemidef
    (Φ : ∀ i j, MatrixChannel (α i) (β j)) (ρ : ∀ i, State (α i))
    {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) (j : ν) :
    (transitionOutput Φ ρ joint j - transitionOutput Φ ρ (keptJoint joint keep) j).PosSemidef := by
  rw [transitionOutput_sub_kept]
  exact transitionOutput_posSemidef Φ ρ (discardedJoint_nonneg hjoint keep) j

/-- The quantum mass discarded within one output sector equals the classical
mass of the deleted input/output pairs. -/
theorem transitionOutput_trace_difference
    (Φ : ∀ i j, MatrixChannel (α i) (β j)) (ρ : ∀ i, State (α i))
    (joint : μ → ν → ℝ) (keep : μ → ν → Prop) (j : ν) :
    (transitionOutput Φ ρ joint j).trace.re -
      (transitionOutput Φ ρ (keptJoint joint keep) j).trace.re =
        ∑ i, discardedJoint joint keep i j := by
  have h := congrArg (fun M : Matrix (β j) (β j) ℂ => M.trace.re)
    (transitionOutput_sub_kept Φ ρ joint keep j)
  simpa only [Matrix.trace_sub, Complex.sub_re, transitionOutput_trace_re] using h

variable [Fintype ν] [DecidableEq ν]
variable {κ : ν → Type*} [∀ j, Fintype (κ j)]
variable [∀ j, DecidableEq (β j)] [∀ j, DecidableEq (κ j)]

/-- Concrete retained-transition estimate: deleting joint mass `δ` changes
the lifted fidelity by at most `√δ`, with canonical retained block states.
The positive-domination premise is proved from the actual masked channel sum. -/
theorem lifted_transition_trimming
    (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (σ : ∀ j, State (β j)) (τ : ∀ j, State (κ j))
    {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) (p : ν → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) :
    |fidelity (liftedOutput Φ ρ τ joint)
        (Matrix.blockDiagonal' (fun j => (p j • (σ j).matrix) ⊗ₖ (τ j).matrix)) -
      ∑ j, Real.sqrt (∑ i, keptJoint joint keep i j) * Real.sqrt (p j) *
        fidelity (normalizedBlock (transitionOutput Φ ρ (keptJoint joint keep) j))
          (σ j).matrix| ≤ Real.sqrt (∑ j, ∑ i, discardedJoint joint keep i j) := by
  have h := lifted_deletion_bound
    (transitionOutput Φ ρ joint) (transitionOutput Φ ρ (keptJoint joint keep))
    (fun j => (σ j).matrix) (fun j => (τ j).matrix) p
    (transitionOutput_posSemidef Φ ρ hjoint)
    (transitionOutput_posSemidef Φ ρ (keptJoint_nonneg hjoint keep))
    (fun j => (σ j).positive) (fun j => (τ j).positive) hp
    (transitionOutput_sub_kept_posSemidef Φ ρ hjoint keep)
    (fun j => by rw [(σ j).trace_one]; rfl)
    (fun j => by rw [(τ j).trace_one]; rfl) hpsum
  simp_rw [transitionOutput_trace_difference] at h
  simpa only [liftedOutput, transitionOutput_trace_re] using h

/-- The finite `η + 2√ε` estimate specialized to genuine channel transitions.
The only sector hypothesis is the fidelity approximation on retained output
states; positivity of the removed contribution is derived from the mask. -/
theorem lifted_transition_factorization_bound
    (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (σ : ∀ j, State (β j)) (τ : ∀ j, State (κ j))
    {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) (p : ν → ℝ) (c η : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hjointmass : ∑ j, ∑ i, joint i j ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ j, 0 < ∑ i, keptJoint joint keep i j →
      |fidelity (normalizedBlock (transitionOutput Φ ρ (keptJoint joint keep) j))
          (σ j).matrix - c| ≤ η) :
    |fidelity (liftedOutput Φ ρ τ joint)
        (Matrix.blockDiagonal' (fun j => (p j • (σ j).matrix) ⊗ₖ (τ j).matrix)) -
      c * Cloning.BlockFidelity.classicalAffinity (fun j => ∑ i, joint i j) p| ≤
      η + 2 * Real.sqrt (∑ j, ∑ i, discardedJoint joint keep i j) := by
  have h := lifted_matrix_factorization_bound
    (transitionOutput Φ ρ joint) (transitionOutput Φ ρ (keptJoint joint keep))
    σ τ p c η (transitionOutput_posSemidef Φ ρ hjoint)
    (transitionOutput_posSemidef Φ ρ (keptJoint_nonneg hjoint keep))
    (transitionOutput_sub_kept_posSemidef Φ ρ hjoint keep) hp hpsum
    (by simpa only [transitionOutput_trace_re] using hjointmass) hc0 hc1 hη
    (by simpa only [transitionOutput_trace_re] using hsector)
  simp_rw [transitionOutput_trace_difference] at h
  simpa only [liftedOutput, transitionOutput_trace_re] using h

end Cloning.MatrixLiftedTrimming
