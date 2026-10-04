import Cloning.PCTRankOneWerner
import Cloning.PhysicalFlatPCTAction

/-! The prescribed rank-one PCT channel is exactly the physical pure-state
Werner cloner on every pure tensor input. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix Kronecker ComplexOrder
namespace Cloning.PCTRankOne
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.PCTRankAdapted
open Cloning.FiniteKrausLift Cloning.InfiniteTraceClass Cloning.PCTPhysicalState
open Cloning.PCTReducedGaussian Cloning.GeneralSymmetricOccupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A : Type*} [Fintype A] [DecidableEq A]

def rankOneVector (J : Matrix A (Fin 1) ℂ) : Register A :=
  matrixRegister J (registerBasis (Fin 1) 0)

@[simp] theorem rankOneVector_apply (J : Matrix A (Fin 1) ℂ) (a : A) :
    rankOneVector J a=J a 0 := by simp [rankOneVector]

theorem rankOneVector_norm (J : Matrix A (Fin 1) ℂ) (hJ : Jᴴ*J=1) :
    ‖rankOneVector J‖=1 := by
  rw [rankOneVector,matrixRegister_norm J hJ]
  exact (registerBasis (Fin 1)).orthonormal.1 0

@[simp] theorem singletonInsertion_apply (ψ : Register A) (a : A) (b : Fin 1) :
    matrixRegister (singletonInsertion (A:=A)) ψ (a,b)=ψ a := by
  simp [matrixRegister_apply,singletonInsertion]

theorem rankOnePurification (J : Matrix A (Fin 1) ℂ) :
    matrixRegister (J⊗ₖ(1 : Matrix (Fin 1) (Fin 1) ℂ))
      (canonicalPurification (flatInternalState 0).matrix)=
      matrixRegister (singletonInsertion (A:=A)) (rankOneVector J) := by
  have hc : canonicalPurification (flatInternalState 0).matrix=
      (lp.single 2 ((0 : Fin 1),(0 : Fin 1)) 1 : Register (Fin 1×Fin 1)) := by
    ext ⟨a,b⟩
    fin_cases a
    fin_cases b
    simp [canonicalPurification,PCTRankPurification.flatInternalState_matrix_complex,
      coefficientVector_apply,lp.single_apply,Pi.single_apply]
  rw [hc]
  ext ⟨a,b⟩
  rw [matrixRegister_single,singletonInsertion_apply,rankOneVector_apply]
  simp [Matrix.kronecker_apply,Subsingleton.elim b (0 : Fin 1)]

variable [Nonempty A]
theorem embeddedPurificationOutput_eq_pureWerner {s : ℕ}
    (hA : Fintype.card A=s+1) (J : Matrix A (Fin 1) ℂ) (hJ : Jᴴ*J=1)
    (n t : ℕ) :
    (embeddedPurificationOutput (by simpa using hA : Fintype.card (A×Fin 1)=s+1)
      J hJ (flatInternalState 0) n t).1=
      pureWernerOutput hA (rankOneVector J) (rankOneVector_norm J hJ)
        (inputSlots n (n+t) (Nat.le_add_right n t)) := by
  unfold embeddedPurificationOutput
  rw [reducedWernerPositive_val]
  simpa only [rankOnePurification] using
    reducedWernerOutput_singleton hA (rankOneVector J) (rankOneVector_norm J hJ)
      (inputSlots n (n+t) (Nat.le_add_right n t))

/-- Finite equality for the fixed, all-input rank-one PCT implementation.
The column is arbitrary; the channel construction does not depend on it. -/
theorem channel_pure_product (k n t : ℕ)
    (J : Matrix (Fin (1+k)) (Fin 1) ℂ) (hJ : Jᴴ*J=1) :
    (Cloning.PhysicalFlatPCT.channel 0 k n t).toLinearMap
      (tensorState (embeddedState J hJ (flatInternalState 0)) n).1=
      pureWernerOutput (by simp [Nat.add_comm] : Fintype.card (Fin (1+k))=k+1)
        (rankOneVector J) (rankOneVector_norm J hJ)
        (inputSlots n (n+t) (Nat.le_add_right n t)) := by
  rw [Cloning.PhysicalFlatPCT.channel_embedded_flatState]
  unfold flatEmbeddedOutput
  simpa only [flatPurificationDimension,Nat.zero_mul,Nat.zero_add,Nat.mul_one] using
    embeddedPurificationOutput_eq_pureWerner (s:=k) (by simp [Nat.add_comm]) J hJ n t

end Cloning.PCTRankOne
