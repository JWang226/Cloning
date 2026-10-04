import Cloning.PCTGlobalMatrixBridge

/-! Rectangular symmetric-sector channels for a smaller purification environment. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation
namespace Cloning.PCTRankGlobal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]
local instance registerFiniteDimensional (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Occupation coordinates embedded into a chosen complete physical frame. -/
def physicalEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B))) (L : ℕ) :
    OccupationSpace L (s + 1) →ₗᵢ[ℂ] Register (Fin L → A × B) :=
  (tensorFrame u.orthonormal L).comp (isometry L (s + 1))

/-- The same occupation embedding with system and environment regrouped. -/
def groupedEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B))) (L : ℕ) :
    OccupationSpace L (s + 1) →ₗᵢ[ℂ] Register ((Fin L → A) × (Fin L → B)) :=
  (regroup L).comp (physicalEmbedding u L)

theorem physicalEmbedding_range {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B))) (L : ℕ) :
    (physicalEmbedding u L).toLinearMap.range = physicalSymmetric L := by
  change ((tensorFrame u.orthonormal L).toLinearMap.comp
    (isometry L (s + 1)).toLinearMap).range = _
  rw [LinearMap.range_comp, isometry_range, physicalSymmetric_map_tensorFrame]

/-- Actual channel compression with a fixed replacement state off the sector. -/
def sectorRecovery {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B))) (n : ℕ) :
    QuantumChannel (Register ((Fin n → A) × (Fin n → B))) (OccupationSpace n (s + 1)) :=
  QuantumChannel.isometricRecovery (groupedEmbedding u n) (vacuumRegister n s)


end Cloning.PCTRankGlobal
