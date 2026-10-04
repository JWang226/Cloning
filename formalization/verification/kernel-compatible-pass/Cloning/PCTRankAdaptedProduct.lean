import Cloning.PCTRankAdaptedStates
import Cloning.PCTPhysicalState

/-! Exact finite-sample product-state fidelity factorization for the literal
rank-adapted purification--Werner--trace output. The separate universal
purification channel supplies the state-independent implementation. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker MatrixOrder ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.GeneralSymmetricOccupation
open Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]

def embeddedState (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ρ : Cloning.MatrixFidelity.State A) : Cloning.MatrixFidelity.State B where
  matrix := J * ρ.matrix * Jᴴ
  positive := ρ.positive.mul_mul_conjTranspose_same J
  trace_one := by rw [Cloning.Compression.trace_isometric_embedding J ρ.matrix hJ, ρ.trace_one]

theorem tensorState_embedded (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ρ : Cloning.MatrixFidelity.State A) (L : ℕ) :
    (tensorState ρ L).map (QuantumChannel.ofIsometry (tensorIsometry L J hJ)).toPositiveTracePreservingMap =
      tensorState (embeddedState J hJ ρ) L := by
  apply Subtype.ext
  change conjugationLinearMap (matrixRegister (tensorPower L J))
    (registerLiftCLM (tensorPower L ρ.matrix)) =
      registerLiftCLM (tensorPower L (J * ρ.matrix * Jᴴ))
  rw [conjugation_matrixRegister, tensorPower_mul, tensorPower_mul, tensorPower_star]

def embeddedPurificationOutput {large : ℕ}
    (hB : Fintype.card (B × A) = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ρ : Cloning.MatrixFidelity.State A) (n t : ℕ) :
    PositiveTraceClass (Register (Fin (n+t) → B)) :=
  reducedWernerPositive hB
    (matrixRegister (J ⊗ₖ (1 : Matrix A A ℂ)) (canonicalPurification ρ.matrix))
    ((matrixRegister_norm _ (systemEmbedding_isometry J hJ) _).trans (canonicalPurification_norm ρ))
    (inputSlots n (n+t) (Nat.le_add_right n t))

theorem outputState_eq_reducedWernerPositive {small : ℕ}
    (hA : Fintype.card (A × A) = small+1)
    (ρ : Cloning.MatrixFidelity.State A) (n t : ℕ) :
    outputState hA ρ n t = reducedWernerPositive hA (canonicalPurification ρ.matrix)
      (canonicalPurification_norm ρ) (inputSlots n (n+t) (Nat.le_add_right n t)) := by
  apply Subtype.ext
  exact Cloning.PCTGlobal.channel_tensorPower hA n t ρ

/-- The exact finite-sample factorization in the projector comparison. It
holds for every internal density, so the maximally mixed specialization
requires no additional state-action or fidelity premise. -/
theorem embeddedPurificationOutput_fidelity_factorization {small large : ℕ}
    (hA : Fintype.card (A × A) = small+1) (hB : Fintype.card (B × A) = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ρ : Cloning.MatrixFidelity.State A) (n t : ℕ) :
    (embeddedPurificationOutput hB J hJ ρ n t).rootFidelity
      (tensorState (embeddedState J hJ ρ) (n+t)) =
    Real.sqrt (supportFactor n (n+t) small large) *
      (outputState hA ρ n t).rootFidelity (tensorState ρ (n+t)) := by
  rw [← tensorState_embedded J hJ ρ (n+t), outputState_eq_reducedWernerPositive]
  exact (reducedWerner_fidelity_factorization hA hB J hJ
    (canonicalPurification ρ.matrix) (canonicalPurification_norm ρ)
    (inputSlots n (n+t) (Nat.le_add_right n t)) (tensorState ρ (n+t))).trans
    (by simp only [inputSlots_card])

end Cloning.PCTRankAdapted
