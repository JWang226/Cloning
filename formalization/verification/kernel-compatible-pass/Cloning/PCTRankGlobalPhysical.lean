import Cloning.PCTRankGlobalRecovery
import Cloning.PCTRankGlobalWerner

/-! The literal rectangular Werner sandwich is realized by one fixed CPTP channel. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner
namespace Cloning.PCTRankGlobal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]
local instance registerFiniteDimensionalPhysical (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The physical Werner sandwich and partial trace as a continuous linear map. -/
def physicalCloneTraceCLM (n r s : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ →L[ℂ]
      TraceClass (Register (Fin (n+r) → A)) :=
  LinearMap.toContinuousLinearMap
    (partialTraceChannel.toLinearMap.comp
      ((QuantumChannel.ofIsometry (regroup (n+r))).toLinearMap.comp
        (((((n+s).choose s : ℝ) / ((n+r+s).choose s : ℝ) : ℝ) : ℂ) •
          (conjugationLinearMap (physicalProjector (C := A × B) (n+r))).comp
            (registerLiftCLM.toLinearMap.comp (slotInsertionCLM n r).toLinearMap))))

theorem matrixOf_tensorProjector (n : ℕ) (ψ : Register (A × B)) :
    matrixOf (registerBasis _) (tensorProjector n ψ).1 =
      fun a c => (regroup n (tensorVector (fun _ : Fin n => ψ))) a *
        star ((regroup n (tensorVector (fun _ : Fin n => ψ))) c) := by
  have h := matrixOf_ofMatrix (registerBasis ((Fin n → A) × (Fin n → B))).orthonormal
    (fun a c => (regroup n (tensorVector (fun _ : Fin n => ψ))) a *
      star ((regroup n (tensorVector (fun _ : Fin n => ψ))) c))
  have he := registerLiftCLM_rankOne (regroup n (tensorVector (fun _ : Fin n => ψ)))
  have hm := congrArg (fun T : TraceClass (Register ((Fin n → A) × (Fin n → B))) =>
    matrixOf (registerBasis _) T.1) he
  exact hm.symm.trans h

theorem slotInsertion_tensorProjector (n r : ℕ) (ψ : Register (A × B)) :
    slotInsertion n r (matrixOf (registerBasis _) (tensorProjector n ψ).1) =
      pureSlotsMatrix ψ (inputSlots n (n+r) (Nat.le_add_right n r)) := by
  rw [matrixOf_tensorProjector]
  ext a c
  rw [pureSlotsMatrix, Fin.prod_univ_add]
  simp only [mem_inputSlots, Fin.val_castAdd, Fin.isLt, if_true,
    Fin.val_natAdd, not_lt_of_ge (Nat.le_add_right n _), if_false,
    slotInsertion, regroup_apply, tensorVector_apply, star_prod, Finset.prod_mul_distrib]

/-- Literal pure-input action of the rectangular downstream map. -/
theorem physicalCloneTraceCLM_tensorProjector (n r s : ℕ)
    (hcard : Fintype.card (A × B) = s+1) (ψ : Register (A × B)) (hψ : ‖ψ‖=1) :
    physicalCloneTraceCLM n r s (matrixOf (registerBasis _) (tensorProjector n ψ).1) =
      reducedWernerOutput hcard ψ hψ (inputSlots n (n+r) (Nat.le_add_right n r)) := by
  have hP : (physicalProjector (C := A × B) (n+r)).adjoint =
      physicalProjector (C := A × B) (n+r) :=
    (isStarProjection_starProjection (U := physicalSymmetric (C := A × B) (n+r))).isSelfAdjoint.adjoint_eq
  simp only [physicalCloneTraceCLM, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    slotInsertionCLM, LinearMap.coe_mk, AddHom.coe_mk]
  rw [slotInsertion_tensorProjector]
  unfold reducedWernerOutput
  congr 2
  apply Subtype.ext
  simp only [pureWernerOutput, TraceClass.ofOperator_coe, pureWernerOperator, inputSlots_card]
  change _ • operatorConjugation (physicalProjector (C := A × B) (n+r))
      (pureSlotsOperator ψ _) = _
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [operatorConjugation_apply, hP, ContinuousLinearMap.mul_apply]

theorem downstreamInFrame_tensorProjector {s : ℕ} (e : Fin (s+1) ≃ A × B)
    (n r : ℕ) (ψ : Register (A × B)) :
    (downstreamInFrame (PCTGlobal.coordinateFrame e) n r).toLinearMap (tensorProjector n ψ) =
      physicalCloneTraceCLM n r s (matrixOf (registerBasis _) (tensorProjector n ψ).1) := by
  rw [downstreamInFrame_matrix_apply, sectorChannel_physical_sandwich,
    recoveredMatrix_embedding_tensorProjector]
  rfl

/-- This frame depends only on the system and environment dimensions. -/
def fixedFrame {s : ℕ} (hcard : Fintype.card (A × B) = s+1) :
    OrthonormalBasis (Fin (s+1)) ℂ (Register (A × B)) :=
  PCTGlobal.coordinateFrame (Fintype.equivFinOfCardEq hcard).symm

/-- A fixed CPTP Werner-clone-and-trace map on every input operator. -/
def downstream {s : ℕ} (hcard : Fintype.card (A × B) = s+1) (n r : ℕ) :
    QuantumChannel (Register ((Fin n → A) × (Fin n → B)))
      (Register (Fin (n+r) → A)) :=
  downstreamInFrame (fixedFrame hcard) n r

/-- The global channel has the exact physical output on every pure tensor input. -/
theorem downstream_tensorProjector {s : ℕ} (hcard : Fintype.card (A × B) = s+1)
    (n r : ℕ) (ψ : Register (A × B)) (hψ : ‖ψ‖=1) :
    (downstream hcard n r).toLinearMap (tensorProjector n ψ) =
      reducedWernerOutput hcard ψ hψ (inputSlots n (n+r) (Nat.le_add_right n r)) := by
  rw [downstream, fixedFrame, downstreamInFrame_tensorProjector,
    physicalCloneTraceCLM_tensorProjector n r s hcard ψ hψ]

end Cloning.PCTRankGlobal
