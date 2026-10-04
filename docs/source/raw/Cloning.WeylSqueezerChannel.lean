import Cloning.WeylSqueezerPreparation
import Cloning.WeylSqueezerPartialTrace
import Cloning.WeylSqueezerUnitaryChannel

/-! Full arbitrary-input amplifier dilation: prepare the joint idler, apply
the genuine doubled-Fock squeeze unitary, and trace out the output idler. -/
noncomputable section
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- A literal composition of three completely positive trace-preserving maps,
valid for arbitrary correlated mixed idlers and all signal states. -/
def channel (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (σ : DensityState (Fock d)) : QuantumChannel (Fock d) (Fock d) :=
  (signalPartialTrace d).comp ((unitaryChannel c s hcs).comp (preparationChannel σ))

/-- The exact signal/idler factorization is derived from the actual dilation,
including complex off-diagonal signal inputs. -/
theorem channel_characteristic (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (σ : DensityState (Fock d)) (T : TraceClass (Fock d)) (a : Fin d → ℂ) :
    tracePairing ((channel c s hcs σ).toLinearMap T) (displacement a)=
      tracePairing (idlerTraceClass σ)
          (displacement (fun i => (s i : ℂ)*(starRingEnd ℂ) (a i)))*
        tracePairing T (displacement (fun i => (c i : ℂ)*a i)) := by
  change tracePairing ((signalPartialTrace d).toLinearMap
    ((unitaryChannel c s hcs).toLinearMap ((preparationChannel σ).toLinearMap T)))
      (displacement a)=_
  rw [signalPartialTrace_characteristic,unitaryChannel_characteristic,transform_signal,
    preparationChannel_characteristic]

end Cloning.WeylSqueezer
