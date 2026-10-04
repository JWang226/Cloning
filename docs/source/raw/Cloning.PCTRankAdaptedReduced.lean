import Cloning.PCTRankAdaptedPartialTrace

/-! Exact support compression of the reduced physical Werner output. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem systemEmbedding_isometry (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1) :
    (J ⊗ₖ (1 : Matrix E E ℂ))ᴴ * (J ⊗ₖ (1 : Matrix E E ℂ)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hJ, Matrix.one_mul, Matrix.one_kronecker_one]

theorem reducedWernerOutput_compression {L small large : ℕ}
    (hA : Fintype.card (A × E) = small+1) (hB : Fintype.card (B × E) = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ψ : Register (A × E)) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    conjugationLinearMap (tensorMap L J).adjoint
      (reducedWernerOutput hB (matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) ψ)
        ((matrixRegister_norm _ (systemEmbedding_isometry J hJ) ψ).trans hψ) S) =
      (supportFactor S.card L small large : ℂ) • reducedWernerOutput hA ψ hψ S := by
  have h := congrArg (reduceOutput (A:=A) (E:=E) L)
    (pureWernerOutput_compression hA hB (J ⊗ₖ (1 : Matrix E E ℂ))
      (systemEmbedding_isometry J hJ) ψ hψ S)
  rw [tensorMap_adjoint, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    reduceOutput_conjugation, ← tensorMap_adjoint L J] at h
  simpa only [reduceOutput, reducedWernerOutput, map_smul] using h

end Cloning.PCTRankAdapted
