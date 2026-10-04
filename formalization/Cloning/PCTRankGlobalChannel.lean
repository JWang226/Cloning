import Cloning.PCTRankGlobalPhysical
import Cloning.PCTRankPurificationNormalization
import Cloning.MatrixLiftedCPTPKraus

/-! The rank-adapted purify--clone--trace protocol as one state-independent CPTP map. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner MeasureTheory
namespace Cloning.PCTRankGlobal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]

/-- The actual Haar-moment purifier, lifted to all trace-class inputs. -/
def purificationChannel (n : ℕ) (J : Matrix A B ℂ)
    (b0 : (Fin n → A) × (Fin n → B)) :
    QuantumChannel (Register (Fin n → A)) (Register ((Fin n → A) × (Fin n → B))) :=
  MatrixLiftedCPTP.registerChannel (PCTRankPurification.rankPurificationChannel n J b0)

theorem purificationChannel_matrix (n : ℕ) (J : Matrix A B ℂ)
    (b0 : (Fin n → A) × (Fin n → B)) (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (purificationChannel n J b0).toLinearMap (registerLiftCLM X) =
      registerLiftCLM ((PCTRankPurification.rankPurificationChannel n J b0).toFun X) :=
  MatrixLiftedCPTP.registerChannel_matrix _ _

/-- The environment dimension and all three stages are fixed before an input is supplied. -/
def channel {s : ℕ} (hcard : Fintype.card (A × B) = s+1)
    (n r : ℕ) (J : Matrix A B ℂ) (b0 : (Fin n → A) × (Fin n → B)) :
    QuantumChannel (Register (Fin n → A)) (Register (Fin (n+r) → A)) :=
  (downstream hcard n r).comp (purificationChannel n J b0)

theorem channel_matrix {s : ℕ} (hcard : Fintype.card (A × B) = s+1)
    (n r : ℕ) (J : Matrix A B ℂ) (b0 : (Fin n → A) × (Fin n → B))
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    (channel hcard n r J b0).toLinearMap (registerLiftCLM X) =
      (downstream hcard n r).toLinearMap
        (registerLiftCLM ((PCTRankPurification.rankPurificationChannel n J b0).toFun X)) := by
  change (downstream hcard n r).toLinearMap
    ((purificationChannel n J b0).toLinearMap (registerLiftCLM X)) = _
  rw [purificationChannel_matrix]

/-- Environment randomization disappears after the actual downstream channel. -/
theorem downstream_randomized {s : ℕ} (hcard : Fintype.card (A × B) = s+1)
    (n r : ℕ) (ψ : Register (A × B)) (hψ : ‖ψ‖=1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Register B →ₗᵢ[ℂ] Register B)
    (hint : Integrable (fun t => tensorProjector n (environmentRotate (W t) ψ)) μ) :
    (downstream hcard n r).toLinearMap
      (∫ t, tensorProjector n (environmentRotate (W t) ψ) ∂μ) =
      reducedWernerOutput hcard ψ hψ (inputSlots n (n+r) (Nat.le_add_right n r)) := by
  let Φ := (downstream hcard n r).toPositiveTracePreservingMap.toContinuousLinearMap
  change Φ (∫ t, tensorProjector n (environmentRotate (W t) ψ) ∂μ) = _
  rw [← Φ.integral_comp_comm hint]
  have he (t : Ω) : Φ (tensorProjector n (environmentRotate (W t) ψ)) =
      reducedWernerOutput hcard ψ hψ (inputSlots n (n+r) (Nat.le_add_right n r)) := by
    change (downstream hcard n r).toLinearMap (tensorProjector n (environmentRotate (W t) ψ)) = _
    rw [downstream_tensorProjector hcard n r _ ((environmentRotate_norm (W t) ψ).trans hψ)]
    exact reducedWernerOutput_environment_invariant hcard ψ hψ (W t) _
  simp_rw [he]
  simp

end Cloning.PCTRankGlobal
