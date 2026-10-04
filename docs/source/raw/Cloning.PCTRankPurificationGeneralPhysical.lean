import Cloning.PCTRankPurificationGeneralOrbit
import Cloning.PCTRankGlobalEmbedding
import Cloning.PCTWernerLower

/-! Exact physical action and the finite Werner lower bound for arbitrary
states embedded in the fixed rank bound. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder InnerProductSpace
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted
open Cloning.InfiniteTraceClass Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.GeneralSymmetricOccupation Cloning.PCTReducedGaussian
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {r : ℕ} [NeZero r]
local instance generalPhysicalAmbientNeZero (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

/-- One fixed channel realizes the literal smaller-environment output for
any embedded density; the density does not choose the channel. -/
theorem channel_embeddedState {s : ℕ} (k n t : ℕ)
    (hcard : Fintype.card (Fin (r+k)×Fin r)=s+1)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (J : Matrix (Fin (r+k)) (Fin r) ℂ) (hJ : Jᴴ*J=1)
    (ρ : Cloning.MatrixFidelity.State (Fin r)) :
    (PCTRankGlobal.channel hcard n t (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toLinearMap
      (tensorState (embeddedState J hJ ρ) n).1 =
      (embeddedPurificationOutput hcard J hJ ρ n t).1 := by
  change (PCTRankGlobal.channel hcard n t _ b0).toLinearMap
    (registerLiftCLM (tensorPower n (J*ρ.matrix*Jᴴ)))=_
  rw [PCTRankGlobal.channel_matrix,rankPurificationChannel_embedded_positive n k b0 J hJ ρ.matrix ρ.positive,
    ← PCTRankGlobal.embeddedHaarCLM_apply]
  exact PCTRankGlobal.downstream_embeddedHaar hcard n t J hJ ρ

variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem reducedDensityMatrix_system (J : Matrix B A ℂ) (ψ : Register (A×E)) :
    reducedDensityMatrix (matrixRegister (J⊗ₖ(1 : Matrix E E ℂ)) ψ)=
      J*reducedDensityMatrix ψ*Jᴴ := by
  let C : Matrix A E ℂ := fun a e=>ψ (a,e)
  have he : matrixRegister (J⊗ₖ(1 : Matrix E E ℂ)) ψ=coefficientVector (J*C) := by
    ext ⟨a,e⟩
    simp only [PCTRankGlobal.matrixRegister_system_apply,coefficientVector_apply,Matrix.mul_apply,C]
  rw [he,reducedDensityMatrix_coefficientVector,Matrix.conjTranspose_mul]
  change (J*C)*(Cᴴ*Jᴴ)=J*(C*Cᴴ)*Jᴴ
  simp only [Matrix.mul_assoc]

variable [Nonempty A] [Nonempty B]

theorem embeddedPurificationOutput_fidelity_lower {s : ℕ}
    (hcard : Fintype.card (B×A)=s+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ*J=1)
    (ρ : Cloning.MatrixFidelity.State A) (n t : ℕ) :
    Real.sqrt (wernerScale n (n+t) s) ≤
      (embeddedPurificationOutput hcard J hJ ρ n t).rootFidelity
        (tensorState (embeddedState J hJ ρ) (n+t)) := by
  apply rootFidelity_lower_of_operator_lower _ _ (norm_tensorState _ _) _
    (wernerScale_pos n (n+t) s).le
  have h := reducedWernerOutput_product_lower hcard
    (matrixRegister (J⊗ₖ(1 : Matrix A A ℂ)) (canonicalPurification ρ.matrix))
    ((matrixRegister_norm _ (systemEmbedding_isometry J hJ) _).trans (canonicalPurification_norm ρ))
    (inputSlots n (n+t) (Nat.le_add_right n t))
  simpa only [inputSlots_card,reducedDensityMatrix_system,canonicalPurification_reduced _ ρ.positive]
    using h

end Cloning.PCTRankPurification
