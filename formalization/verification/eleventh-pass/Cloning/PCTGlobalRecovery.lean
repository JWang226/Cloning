import Cloning.PCTGlobalChannels

/-! Symmetric occupation recovery is exact on every Haar purification output,
including nonpositive inputs. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner

namespace Cloning.PCTGlobal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
local instance registerFiniteDimensionalRecovery (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem registerLiftCLM_matrixOf {I : Type*} [Fintype I] [DecidableEq I]
    (T : TraceClass (Register I)) :
    registerLiftCLM (matrixOf (registerBasis I) T.1) = T :=
  Subtype.ext (PurificationSupport.ofMatrix_matrixOf_register T.1)

theorem purification_projection_support (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    conjugationLinearMap (PurificationSupport.groupedSymmetric (A := A) n).starProjection
      (registerLiftCLM ((haarPurificationChannel n).toFun X)) =
        registerLiftCLM ((haarPurificationChannel n).toFun X) := by
  have hP : FiniteKrausLift.matrixRegister (PurificationSupport.symmetricMatrix (A := A) n) =
      (PurificationSupport.groupedSymmetric (A := A) n).starProjection := by
    rw [← FiniteKrausLift.registerLiftCLM_operator]
    exact PurificationSupport.ofMatrix_symmetricMatrix n
  rw [← hP, FiniteKrausLift.conjugation_matrixRegister,
    PurificationSupport.symmetricMatrix_conjTranspose,
    PurificationSupport.haarPurificationChannel_supported]

theorem conjugation_comp {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (V : K →L[ℂ] L) (W : H →L[ℂ] K) (T : TraceClass H) :
    conjugationLinearMap V (conjugationLinearMap W T) = conjugationLinearMap (V.comp W) T := by
  apply Subtype.ext
  ext x
  simp only [conjugationLinearMap_coe, operatorConjugation_apply,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

/-- Adjoint compression followed by embedding exactly preserves every
purification output; the arbitrary complex input is unrestricted. -/
theorem purification_compression_embedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    conjugationLinearMap (groupedEmbedding u n).toContinuousLinearMap
      (conjugationLinearMap (groupedEmbedding u n).toContinuousLinearMap.adjoint
        (registerLiftCLM ((haarPurificationChannel n).toFun X))) =
      registerLiftCLM ((haarPurificationChannel n).toFun X) := by
  rw [conjugation_comp, groupedEmbedding_projection, purification_projection_support]

/-- The replacement term in the global recovery channel is exactly zero
on every output of the fixed Haar purification channel. -/
theorem sectorRecovery_purification {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (sectorRecovery u n).toLinearMap
      (registerLiftCLM ((haarPurificationChannel n).toFun X)) =
      conjugationLinearMap (groupedEmbedding u n).toContinuousLinearMap.adjoint
        (registerLiftCLM ((haarPurificationChannel n).toFun X)) := by
  have ht := congrArg traceCLM (purification_compression_embedding u n X)
  rw [conjugationLinearMap_isometry_trace] at ht
  rw [sectorRecovery, QuantumChannel.isometricRecovery_apply, ht, sub_self,
    zero_smul, add_zero]

theorem sectorRecovery_purification_embedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    conjugationLinearMap (groupedEmbedding u n).toContinuousLinearMap
      ((sectorRecovery u n).toLinearMap
        (registerLiftCLM ((haarPurificationChannel n).toFun X))) =
      registerLiftCLM ((haarPurificationChannel n).toFun X) := by
  rw [sectorRecovery_purification, purification_compression_embedding]

/-- Every trace-class input is covered, since the finite register matrix
coordinates reconstruct its operator exactly. -/
theorem sectorRecovery_purification_all {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (T : TraceClass (Register (Fin n → A))) :
    (QuantumChannel.ofIsometry (groupedEmbedding u n)).toLinearMap
      ((sectorRecovery u n).toLinearMap ((purificationChannel n).toLinearMap T)) =
        (purificationChannel n).toLinearMap T := by
  obtain ⟨X, rfl⟩ : ∃ X : Matrix (Fin n → A) (Fin n → A) ℂ,
      registerLiftCLM X = T := ⟨matrixOf (registerBasis _) T.1, registerLiftCLM_matrixOf T⟩
  rw [purificationChannel_apply]
  exact sectorRecovery_purification_embedding u n X

/-- A completely positive trace-preserving full PCT protocol, independent
of the unknown density input. -/
def channelInFrame {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n r : ℕ) :
    QuantumChannel (Register (Fin n → A)) (Register (Fin (n + r) → A)) :=
  partialTraceChannel.comp ((QuantumChannel.ofIsometry (regroup (n + r))).comp
    ((QuantumChannel.ofIsometry (physicalEmbedding u (n + r))).comp
      ((sectorChannel n r s).comp ((sectorRecovery u n).comp (purificationChannel n)))))

end Cloning.PCTGlobal
