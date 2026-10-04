import Cloning.WeylSqueezerProductSlices
import Cloning.WeylSqueezerKraus

/-! The actual partial-trace channels on either half of the doubled Fock
register, with exact all-input Weyl characteristic identities. -/
noncomputable section
open scoped Topology InnerProductSpace
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass Cloning.WeylSqueezerProduct
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def signalPartialTrace (d : ℕ) : QuantumChannel (Fock (d+d)) (Fock d) :=
  QuantumChannel.ofRectangularKraus (signalSlice (a := d) (b := d))
    (fun x => signalSlice_norm_sq_hasSum (a := d) (b := d) x)

def idlerPartialTrace (d : ℕ) : QuantumChannel (Fock (d+d)) (Fock d) :=
  QuantumChannel.ofRectangularKraus (idlerSlice (a := d) (b := d))
    (fun x => idlerSlice_norm_sq_hasSum (a := d) (b := d) x)

theorem signalPartialTrace_characteristic (T : TraceClass (Fock (d+d))) (a : Fin d → ℂ) :
    tracePairing ((signalPartialTrace d).toLinearMap T) (displacement a)=
      tracePairing T (displacement (Fin.append a 0)) := by
  have hpure (x : Fock (d+d)) :
      tracePairing ((signalPartialTrace d).toLinearMap (vectorProjector x)) (displacement a)=
        1*⟪x,displacement (Fin.append a 0) x⟫_ℂ := by
    have hs := rectangularKraus_pairing_pure_hasSum (signalSlice (a := d) (b := d))
      (fun y => signalSlice_norm_sq_hasSum (a := d) (b := d) y) x (displacement a)
    have ht := signalSlice_inner_hasSum (a := d) (b := d) x (displacement (Fin.append a 0) x)
    simp only [signalSlice_displacement] at ht
    simpa only [one_mul] using hs.unique ht
  simpa only [one_mul] using
    channel_pairing_of_pure (signalPartialTrace d) (displacement a)
      (displacement (Fin.append a 0)) 1 hpure T

theorem idlerPartialTrace_characteristic (T : TraceClass (Fock (d+d))) (b : Fin d → ℂ) :
    tracePairing ((idlerPartialTrace d).toLinearMap T) (displacement b)=
      tracePairing T (displacement (Fin.append 0 b)) := by
  have hpure (x : Fock (d+d)) :
      tracePairing ((idlerPartialTrace d).toLinearMap (vectorProjector x)) (displacement b)=
        1*⟪x,displacement (Fin.append 0 b) x⟫_ℂ := by
    have hs := rectangularKraus_pairing_pure_hasSum (idlerSlice (a := d) (b := d))
      (fun y => idlerSlice_norm_sq_hasSum (a := d) (b := d) y) x (displacement b)
    have ht := idlerSlice_inner_hasSum (a := d) (b := d) x (displacement (Fin.append 0 b) x)
    simp only [idlerSlice_displacement] at ht
    simpa only [one_mul] using hs.unique ht
  simpa only [one_mul] using
    channel_pairing_of_pure (idlerPartialTrace d) (displacement b)
      (displacement (Fin.append 0 b)) 1 hpure T

end Cloning.WeylSqueezer
