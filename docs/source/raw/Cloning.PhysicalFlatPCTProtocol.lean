import Cloning.PCTRankGlobalEmbedding
import Cloning.PhysicalFlatGrassmannIsometry

/-! A single rank-adapted PCT channel and its outputs on every literal
rank-r projector. The construction does not depend on the input projector. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Cloning.PhysicalFlatPCT
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PhysicalFlatGrassmann Cloning.PCTRankAdapted Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
local instance (d k : ℕ) : Nonempty (Fin (d+1+k)) := ⟨⟨0,by omega⟩⟩

/-- All stages use the fixed coordinate inclusion and fixed computational
fallback. In particular no unknown projector or eigenbasis occurs here. -/
def channel (d k n t : ℕ) :
    QuantumChannel (Register (Fin n → Fin (d+1+k))) (Register (Fin (n+t) → Fin (d+1+k))) :=
  PCTRankGlobal.channel (flat_ambient_register_card d k) n t
    (coordinateInclusion (d+1) k) (fun _ => ⟨0,by omega⟩, fun _ => ⟨0,by omega⟩)

/-- Literal output of the prescribed all-input CPTP map on a normalized
orthogonal-projector product state. -/
def outputState (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) :
    PositiveTraceClass (Register (Fin (n+t) → Fin (d+1+k))) :=
  (tensorState (state (by omega : 0<d+1) P) n).map (channel d k n t).toPositiveTracePreservingMap

/-- Root fidelity against the requested literal projector product state. -/
def fidelity (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) : ℝ :=
  (outputState d k P n t).rootFidelity (tensorState (state (by omega : 0<d+1) P) (n+t))

theorem fidelity_nonneg (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) :
    0 ≤ fidelity d k P n t := PositiveTraceClass.rootFidelity_nonneg _ _

theorem fidelity_le_one (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) :
    fidelity d k P n t ≤ 1 := by
  change Cloning.TensorCloning.statePayoff n (n+t) (channel d k n t)
    (state (by omega : 0<d+1) P) ≤ 1
  exact Cloning.TensorCloning.statePayoff_le_one _ _ _ _

end Cloning.PhysicalFlatPCT
