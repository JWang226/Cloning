import Cloning.PCTRankAdaptedFidelity

/-! Positive physical reduced Werner states and their exact support-fidelity
factorization. The states are literal Werner outputs followed by partial trace. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.GeneralSymmetricOccupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem pureWernerOutput_nonneg {L s : ℕ} (hcard : Fintype.card A = s+1)
    (ψ : Register A) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    0 ≤ (pureWernerOutput hcard ψ hψ S).1 := by
  obtain ⟨u,hu⟩ := exists_purification_frame hcard ψ hψ
  subst ψ
  rw [pureWernerOutput_eq_frame hcard u.orthonormal]
  exact (QuantumChannel.ofIsometry (tensorFrame u.orthonormal L)).map_nonneg _
    (wernerOutput_nonneg S)

def pureWernerPositive {L s : ℕ} (hcard : Fintype.card A = s+1)
    (ψ : Register A) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    PositiveTraceClass (Register (Fin L → A)) :=
  ⟨pureWernerOutput hcard ψ hψ S,pureWernerOutput_nonneg hcard ψ hψ S⟩

def reducedWernerPositive {L s : ℕ} (hcard : Fintype.card (A × E) = s+1)
    (ψ : Register (A × E)) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    PositiveTraceClass (Register (Fin L → A)) :=
  (pureWernerPositive hcard ψ hψ S).map
    (partialTraceChannel.comp (QuantumChannel.ofIsometry (regroup L))).toPositiveTracePreservingMap

@[simp] theorem reducedWernerPositive_val {L s : ℕ}
    (hcard : Fintype.card (A × E) = s+1)
    (ψ : Register (A × E)) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    (reducedWernerPositive hcard ψ hψ S).1 = reducedWernerOutput hcard ψ hψ S := rfl

theorem tensorPower_isometry (L : ℕ) (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1) :
    (tensorPower L J)ᴴ * tensorPower L J = 1 := by
  rw [← tensorPower_star, ← tensorPower_mul, hJ, tensorPower_one]

def tensorIsometry (L : ℕ) (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1) :
    Register (Fin L → A) →ₗᵢ[ℂ] Register (Fin L → B) :=
  matrixIsometry (tensorPower L J) (tensorPower_isometry L J hJ)

/-- Finite-sample factorization for an arbitrary embedded purification and
any target state on the smaller physical system. -/
theorem reducedWerner_fidelity_factorization {L small large : ℕ}
    (hA : Fintype.card (A × E) = small+1) (hB : Fintype.card (B × E) = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ψ : Register (A × E)) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L))
    (Y : PositiveTraceClass (Register (Fin L → A))) :
    (reducedWernerPositive hB (matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ)) ψ)
      ((matrixRegister_norm _ (systemEmbedding_isometry J hJ) ψ).trans hψ) S).rootFidelity
      (Y.map (QuantumChannel.ofIsometry (tensorIsometry L J hJ)).toPositiveTracePreservingMap) =
    Real.sqrt (supportFactor S.card L small large) *
      (reducedWernerPositive hA ψ hψ S).rootFidelity Y := by
  apply rootFidelity_of_compression (tensorPower L J) (tensorPower_isometry L J hJ)
    _ _ Y _ (supportFactor_pos S.card L small large).le
  exact reducedWernerOutput_compression hA hB J hJ ψ hψ S

end Cloning.PCTRankAdapted
