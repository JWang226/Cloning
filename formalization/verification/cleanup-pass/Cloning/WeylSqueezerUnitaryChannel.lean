import Cloning.WeylSqueezerUnitary
import Cloning.WeylQuantumPositiveBlocks

/-! The actual two-register unitary quantum channel and its exact action on
every bounded Weyl observable. -/
noncomputable section
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def unitaryChannel (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1) :
    QuantumChannel (Fock (d+d)) (Fock (d+d)) :=
  QuantumChannel.ofIsometry (squeeze c s hcs).toLinearIsometry

theorem unitaryChannel_characteristic (c s : Fin d → ℝ) (hcs : ∀i,c i^2-s i^2=1)
    (T : TraceClass (Fock (d+d))) (a : Fin (d+d) → ℂ) :
    tracePairing ((unitaryChannel c s hcs).toLinearMap T) (displacement a)=
      tracePairing T (displacement (transform c s a)) := by
  change tracePairing (conjugationLinearMap
    (squeeze c s hcs : Fock (d+d) →L[ℂ] Fock (d+d)) T) (displacement a)=_
  rw [tracePairing_conjugation,squeeze_heisenberg]

end Cloning.WeylSqueezer
