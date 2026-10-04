import Cloning.PCTPrescribedExtension
import Cloning.PhysicalCloningPCTTheorem

/-! The physical full-rank PCT theorem for arbitrary requested output sizes,
with exact partial trace below the cloning regime. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.PCTPrescribed
open Cloning.PCT Cloning.TensorLie Cloning.TensorCloning Cloning.InfiniteTraceClass
open Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- State-independent full-environment PCT, defined for every pair n,m. -/
def fullChannel (d n m : ℕ) :
    QuantumChannel (TensorRegister n (Fin (d+1))) (TensorRegister m (Fin (d+1))) :=
  extendChannel (fun n t => PCTGlobal.channel (purification_register_card d) n t) n m

theorem fullChannel_of_le (d n m : ℕ) (h : m≤n) :
    fullChannel d n m=restrictionChannel n m (d+1) h := extendChannel_of_le _ n m h

theorem fullChannel_tensorState_of_le (d n m : ℕ) (h : m≤n)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1))) :
    (fullChannel d n m).toLinearMap (tensorState ρ n).1=(tensorState ρ m).1 :=
  extendChannel_tensorState_of_le _ n m h ρ

theorem fullChannel_self (d n : ℕ) (X : TraceClass (TensorRegister n (Fin (d+1)))) :
    (fullChannel d n n).toLinearMap X=X := extendChannel_self _ n X

/-- No eventual sample-size inequality is assumed: it follows from γ>1.
The physical density and eigenbasis are arbitrary. -/
theorem fullChannel_fidelity_tendsto {d : ℕ} (hd : 1≤d)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1))) (hpos : ρ.matrix.PosDef)
    (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n => statePayoff n (m n) (fullChannel d n (m n)) ρ) atTop
      (𝓝 (Cloning.pctValue γ (densitySpectrum ρ hpos hsimple))) := by
  have h := physical_pct_fidelity hd ρ hpos hsimple (fun n => m n-n) γ hγ
    (addedCopies_ratio m hγ hgain)
  exact h.congr' (eventually_extendChannel_payoff
    (fun n t => PCTGlobal.channel (purification_register_card d) n t) ρ m hγ hgain)

end Cloning.PCTPrescribed
