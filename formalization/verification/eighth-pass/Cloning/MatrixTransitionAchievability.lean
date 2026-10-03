import Cloning.MatrixLiftedTrimming
import Cloning.MatrixFidelityMixtures
import Cloning.MatrixFidelityAchievability

/-!
# Achievability for actual finite matrix-channel transitions

Every retained normalized block is explicitly a probability mixture of the
individual channel outputs. Concavity transfers a uniform lower fidelity
bound through that mixture. It does not assert an upper bound or an exact
limit for the mixture fidelity.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix
open Cloning.Channels Cloning.MatrixFidelity
open Cloning.MatrixLiftedChannel Cloning.MatrixLiftedTrimming

namespace Cloning.MatrixTransitionAchievability

set_option backward.isDefEq.respectTransparency false

variable {μ ν : Type*} [Fintype μ]
variable {α : μ → Type*} {β : ν → Type*}
variable [∀ i, Fintype (α i)] [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]

omit [∀ j, DecidableEq (β j)] in
/-- The canonical normalized output equals the explicit mixture with
conditional transition weights. The identity also holds at zero marginal. -/
theorem normalized_transitionOutput_eq_mixture
    (Φ : ∀ i j, MatrixChannel (α i) (β j)) (ρ : ∀ i, State (α i))
    (joint : μ → ν → ℝ) (j : ν) :
    normalizedBlock (transitionOutput Φ ρ joint j) =
      ∑ i, (joint i j / ∑ k, joint k j) • (Φ i j).toFun (ρ i).matrix := by
  unfold normalizedBlock
  rw [transitionOutput_trace_re]
  unfold transitionOutput
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

omit [∀ j, DecidableEq (β j)] in
theorem conditional_weights_nonneg {joint : μ → ν → ℝ}
    (hjoint : ∀ i j, 0 ≤ joint i j) {j : ν} (hq : 0 < ∑ i, joint i j) :
    ∀ i, 0 ≤ joint i j / ∑ k, joint k j :=
  fun i => div_nonneg (hjoint i j) hq.le

omit [∀ j, DecidableEq (β j)] in
theorem conditional_weights_sum {joint : μ → ν → ℝ} {j : ν}
    (hq : 0 < ∑ i, joint i j) : (∑ i, joint i j / ∑ k, joint k j) = 1 := by
  rw [← Finset.sum_div, div_self (ne_of_gt hq)]

/-- Uniform lower fidelity on retained positive-weight transitions passes to
the normalized output block by concrete matrix-fidelity concavity. -/
theorem retained_transition_fidelity_lower
    (Φ : ∀ i j, MatrixChannel (α i) (β j)) (ρ : ∀ i, State (α i))
    {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) (j : ν) (T : Matrix (β j) (β j) ℂ) (c : ℝ)
    (hq : 0 < ∑ i, keptJoint joint keep i j)
    (hindividual : ∀ i, keep i j → 0 < joint i j →
      c ≤ fidelity ((Φ i j).toFun (ρ i).matrix) T) :
    c ≤ fidelity (normalizedBlock (transitionOutput Φ ρ (keptJoint joint keep) j)) T := by
  classical
  rw [normalized_transitionOutput_eq_mixture]
  apply fidelity_finite_mixture_lower
    (fun i => (Φ i j).toFun (ρ i).matrix) T
    (fun i => keptJoint joint keep i j / ∑ k, keptJoint joint keep k j) c
    (fun i => map_positive (Φ i j) (ρ i).positive)
    (conditional_weights_nonneg (keptJoint_nonneg hjoint keep) hq)
    (conditional_weights_sum hq)
  intro i hi
  have hki : 0 < keptJoint joint keep i j :=
    (div_pos_iff_of_pos_right hq).mp hi
  by_cases hkeep : keep i j
  · exact hindividual i hkeep (by simpa only [keptJoint, if_pos hkeep] using hki)
  · simp only [keptJoint, if_neg hkeep, lt_self_iff_false] at hki

variable [Fintype ν] [DecidableEq ν]
variable {κ : ν → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]

/-- Concrete finite achievability from lower bounds on the individual retained
channel outputs. Mixing within one output sector is justified by concavity,
and deleting arbitrary sector pairs costs only the square root of their mass.
This is a lower bound; no equality or mixture upper bound is asserted. -/
theorem transition_achievability_bound
    (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (ρ : ∀ i, State (α i)) (σ : ∀ j, State (β j)) (τ : ∀ j, State (κ j))
    {joint : μ → ν → ℝ} (hjoint : ∀ i j, 0 ≤ joint i j)
    (keep : μ → ν → Prop) (p : ν → ℝ) (c η : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hjointmass : ∑ j, ∑ i, joint i j ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hindividual : ∀ i j, keep i j → 0 < joint i j →
      c - η ≤ fidelity ((Φ i j).toFun (ρ i).matrix) (σ j).matrix) :
    c * Cloning.BlockFidelity.classicalAffinity (fun j => ∑ i, joint i j) p - η -
      Real.sqrt (∑ j, ∑ i, discardedJoint joint keep i j) ≤
      fidelity (liftedOutput Φ ρ τ joint)
        (Matrix.blockDiagonal' (fun j => (p j • (σ j).matrix) ⊗ₖ (τ j).matrix)) := by
  have hsectorLower : ∀ j,
      0 < (transitionOutput Φ ρ (keptJoint joint keep) j).trace.re →
      c - η ≤ fidelity
        (normalizedBlock (transitionOutput Φ ρ (keptJoint joint keep) j)) (σ j).matrix := by
    intro j hj
    exact retained_transition_fidelity_lower Φ ρ hjoint keep j (σ j).matrix (c - η)
      (by simpa only [transitionOutput_trace_re] using hj)
      (fun i hkeep hij => hindividual i j hkeep hij)
  have h := fidelity_lifted_achievability
    (transitionOutput Φ ρ joint) (transitionOutput Φ ρ (keptJoint joint keep))
    (fun j => (σ j).matrix) (fun j => (τ j).matrix) p c η
    (transitionOutput_posSemidef Φ ρ hjoint)
    (transitionOutput_posSemidef Φ ρ (keptJoint_nonneg hjoint keep))
    (fun j => (σ j).positive) (fun j => (τ j).positive) hp
    (fun j => by rw [(τ j).trace_one]; rfl) hpsum
    (by simpa only [transitionOutput_trace_re] using hjointmass)
    (fun j => show transitionOutput Φ ρ (keptJoint joint keep) j ≤
      transitionOutput Φ ρ joint j from transitionOutput_sub_kept_posSemidef Φ ρ hjoint keep j)
    hc0 hc1 hη hsectorLower
  simp_rw [transitionOutput_trace_difference] at h
  simpa only [liftedOutput, transitionOutput_trace_re] using h

end Cloning.MatrixTransitionAchievability
