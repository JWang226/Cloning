import Cloning.PCTRankGlobalMatrixBridge

/-! Exact rectangular symmetric-sector recovery on every pure tensor input. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner
namespace Cloning.PCTRankGlobal
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]
local instance registerFiniteDimensionalRecovery (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The literal grouped pure tensor projector. -/
def tensorProjector (n : ℕ) (ψ : Register (A × B)) :
    TraceClass (Register ((Fin n → A) × (Fin n → B))) :=
  vectorProjector (regroup n (tensorVector (fun _ : Fin n => ψ)))

theorem tensorVector_mem_physicalSymmetric (n : ℕ) (ψ : Register (A × B)) :
    tensorVector (fun _ : Fin n => ψ) ∈ physicalSymmetric n := by
  intro w σ
  change (∏ i, ψ (w (σ i))) = ∏ i, ψ (w i)
  exact Equiv.prod_comp σ (fun i => ψ (w i))

theorem tensorVector_in_groupedEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B)))
    (n : ℕ) (ψ : Register (A × B)) :
    ∃ x, groupedEmbedding u n x = regroup n (tensorVector (fun _ : Fin n => ψ)) := by
  have h := tensorVector_mem_physicalSymmetric n ψ
  rw [← physicalEmbedding_range u n] at h
  obtain ⟨x,hx⟩ := h
  exact ⟨x,congrArg (regroup n) hx⟩

/-- Recovery followed by embedding fixes the actual tensor projector exactly. -/
theorem sectorRecovery_tensorProjector_embedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B)))
    (n : ℕ) (ψ : Register (A × B)) :
    conjugationLinearMap (groupedEmbedding u n).toContinuousLinearMap
      ((sectorRecovery u n).toLinearMap (tensorProjector n ψ)) = tensorProjector n ψ := by
  obtain ⟨x,hx⟩ := tensorVector_in_groupedEmbedding u n ψ
  unfold tensorProjector
  rw [← hx, sectorRecovery, QuantumChannel.isometricRecovery_vectorProjector]
  exact conjugationLinearMap_vectorProjector _ x

/-- A genuine all-input channel for cloning a purification and tracing its environment. -/
def downstreamInFrame {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B))) (n r : ℕ) :
    QuantumChannel (Register ((Fin n → A) × (Fin n → B)))
      (Register (Fin (n+r) → A)) :=
  partialTraceChannel.comp ((QuantumChannel.ofIsometry (regroup (n+r))).comp
    ((QuantumChannel.ofIsometry (physicalEmbedding u (n+r))).comp
      ((PCTGlobal.sectorChannel n r s).comp (sectorRecovery u n))))

def recoveredMatrix {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B))) (n : ℕ)
    (T : TraceClass (Register ((Fin n → A) × (Fin n → B)))) :
    Matrix (Occupation n (s+1)) (Occupation n (s+1)) ℂ :=
  matrixOf (registerBasis _) ((sectorRecovery u n).toLinearMap T).1

theorem recoveredMatrix_lift {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B))) (n : ℕ)
    (T : TraceClass (Register ((Fin n → A) × (Fin n → B)))) :
    registerLiftCLM (recoveredMatrix u n T) = (sectorRecovery u n).toLinearMap T :=
  PCTGlobal.registerLiftCLM_matrixOf _

theorem recoveredMatrix_embedding_tensorProjector {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B))) (n : ℕ)
    (ψ : Register (A × B)) :
    matrixOf (registerBasis _)
      (operatorConjugation (groupedEmbedding u n).toContinuousLinearMap
        (registerLiftCLM (recoveredMatrix u n (tensorProjector n ψ))).1) =
      matrixOf (registerBasis _) (tensorProjector n ψ).1 := by
  have he := sectorRecovery_tensorProjector_embedding u n ψ
  rw [← recoveredMatrix_lift u n (tensorProjector n ψ)] at he
  exact congrArg (fun T : TraceClass (Register ((Fin n → A) × (Fin n → B))) =>
    matrixOf (registerBasis _) T.1) he

theorem downstreamInFrame_matrix_apply {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B))) (n r : ℕ)
    (T : TraceClass (Register ((Fin n → A) × (Fin n → B)))) :
    (downstreamInFrame u n r).toLinearMap T =
      partialTraceChannel.toLinearMap
        ((QuantumChannel.ofIsometry (regroup (n+r))).toLinearMap
          (conjugationLinearMap (physicalEmbedding u (n+r)).toContinuousLinearMap
            ((PCTGlobal.sectorChannel n r s).toLinearMap
              (registerLiftCLM (recoveredMatrix u n T))))) := by
  rw [recoveredMatrix_lift]
  rfl

end Cloning.PCTRankGlobal
