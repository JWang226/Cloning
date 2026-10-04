import Cloning.PCTPrescribedExtension
import Cloning.PhysicalFlatPCTProtocol

/-! One fixed rank-adapted PCT protocol for arbitrary input-output sample
sizes, with exact physical restriction when m≤n. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PCTPrescribed
open Cloning.PCT Cloning.TensorLie Cloning.TensorCloning Cloning.InfiniteTraceClass
open Cloning.PCTPhysicalState Cloning.PhysicalFlatGrassmann
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance rankAmbientNonempty (d k : ℕ) : Nonempty (Fin (d+1+k)) := ⟨⟨0,by omega⟩⟩

/-- The channel is chosen before the unknown projector is supplied. -/
def rankChannel (d k n m : ℕ) :
    QuantumChannel (TensorRegister n (Fin (d+1+k))) (TensorRegister m (Fin (d+1+k))) :=
  extendChannel (PhysicalFlatPCT.channel d k) n m

def rankFidelity (d k : ℕ) (P : Projector (d+1) k) (n m : ℕ) : ℝ :=
  statePayoff n m (rankChannel d k n m) (state (by omega : 0<d+1) P)

theorem rankChannel_of_le (d k n m : ℕ) (h : m≤n) :
    rankChannel d k n m=restrictionChannel n m (d+1+k) h := extendChannel_of_le _ n m h

theorem rankChannel_tensorState_of_le (d k n m : ℕ) (h : m≤n)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1+k))) :
    (rankChannel d k n m).toLinearMap (tensorState ρ n).1=(tensorState ρ m).1 :=
  extendChannel_tensorState_of_le _ n m h ρ

theorem rankChannel_self (d k n : ℕ) (X : TraceClass (TensorRegister n (Fin (d+1+k)))) :
    (rankChannel d k n n).toLinearMap X=X := extendChannel_self _ n X

theorem eventually_rankFidelity (d k : ℕ) (P : Projector (d+1) k)
    (m : ℕ → ℕ) {γ : ℝ} (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    (fun n => PhysicalFlatPCT.fidelity d k P n (m n-n)) =ᶠ[atTop]
      (fun n => rankFidelity d k P n (m n)) :=
  eventually_extendChannel_payoff (PhysicalFlatPCT.channel d k)
    (state (by omega : 0<d+1) P) m hγ hgain

end Cloning.PCTPrescribed
