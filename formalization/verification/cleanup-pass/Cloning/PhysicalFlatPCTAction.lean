import Cloning.PCTRankPurificationFlatState
import Cloning.PhysicalFlatPCTProtocol

/-! Exact action of the fixed smaller-environment PCT channel on every
rank-flat input, derived from the actual normalized Haar purifier. -/
noncomputable section
open scoped Matrix Kronecker ComplexOrder
namespace Cloning.PhysicalFlatPCT
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.PhysicalFlatGrassmann
open Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance actionAmbientNeZero (d k : ℕ) : NeZero (d+1+k) := ⟨by omega⟩

theorem channel_embedded_flatState (d k n t : ℕ)
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1) :
    (channel d k n t).toLinearMap (tensorState (embeddedState J hJ (flatInternalState d)) n).1 =
      (flatEmbeddedOutput d k J hJ n t).1 := by
  change (PCTRankGlobal.channel (flat_ambient_register_card d k) n t
    (coordinateInclusion (d+1) k) (fun _ => ⟨0,by omega⟩, fun _ => ⟨0,by omega⟩)).toLinearMap
      (registerLiftCLM (tensorPower n (embeddedState J hJ (flatInternalState d)).matrix)) = _
  rw [PCTRankGlobal.channel_matrix]
  change (PCTRankGlobal.downstream (flat_ambient_register_card d k) n t).toLinearMap
    (registerLiftCLM ((PCTRankPurification.rankPurificationChannel n
      (Cloning.TensorLie.coordinateInclusionMatrix (d+1) k)
      (fun _ => ⟨0,by omega⟩, fun _ => ⟨0,by omega⟩)).toFun
      (tensorPower n (embeddedState J hJ (flatInternalState d)).matrix))) = _
  rw [PCTRankPurification.rankPurificationChannel_flatState]
  rw [← PCTRankGlobal.embeddedHaarCLM_apply]
  exact PCTRankGlobal.downstream_embeddedHaar (flat_ambient_register_card d k) n t J hJ (flatInternalState d)

theorem outputState_eq_flatEmbeddedOutput (d k : ℕ) (P : Projector (d+1) k)
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1)
    (hP : state (by omega : 0<d+1) P=embeddedState J hJ (flatInternalState d)) (n t : ℕ) :
    outputState d k P n t=flatEmbeddedOutput d k J hJ n t := by
  apply Subtype.ext
  change (channel d k n t).toLinearMap (tensorState (state (by omega : 0<d+1) P) n).1 = _
  rw [hP]
  exact channel_embedded_flatState d k n t J hJ

end Cloning.PhysicalFlatPCT
