import Cloning.InfiniteRectangularKraus
import Cloning.HeisenbergDual

/-! Exact bounded-observable formulas for actual Kraus channels. -/
noncomputable section
open scoped InnerProductSpace Topology
namespace Cloning.WeylSqueezer
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {ι H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem rectangularKraus_pairing_pure_hasSum
    (V : ι → H →L[ℂ] K) (hV : RectangularKrausComplete V)
    (x : H) (A : K →L[ℂ] K) :
    HasSum (fun i => ⟪V i x,A (V i x)⟫_ℂ)
      (tracePairing ((QuantumChannel.ofRectangularKraus V hV).toLinearMap
        (vectorProjector x)) A) := by
  have hh := (QuantumChannel.ofRectangularKraus_vectorProjector_hasSum V hV x).mapL
    (tracePairingCLM.flip A)
  change HasSum (fun i => tracePairing (vectorProjector (V i x)) A) _ at hh
  have he (i : ι) : tracePairing (vectorProjector (V i x)) A=⟪V i x,A (V i x)⟫_ℂ :=
    tracePairing_rankOneOperator _ _ A
  simpa only [he] using hh

/-- A bounded-observable identity verified on every pure vector extends to all
complex trace-class inputs, including arbitrary mixed states and coherences. -/
theorem channel_pairing_of_pure (Φ : QuantumChannel H K)
    (A : K →L[ℂ] K) (B : H →L[ℂ] H) (c : ℂ)
    (hpure : ∀x : H,tracePairing (Φ.toLinearMap (vectorProjector x)) A=
      c*⟪x,B x⟫_ℂ) (T : TraceClass H) :
    tracePairing (Φ.toLinearMap T) A=c*tracePairing T B := by
  have he : (tracePairingCLM.flip A).comp
      Φ.toPositiveTracePreservingMap.toContinuousLinearMap=c • tracePairingCLM.flip B := by
    apply traceClass_functional_ext
    intro x
    change tracePairing (Φ.toLinearMap (vectorProjector x)) A=
      c*tracePairing (vectorProjector x) B
    rw [show tracePairing (vectorProjector x) B=⟪x,B x⟫_ℂ from tracePairing_rankOneOperator x x B]
    exact hpure x
  exact congrArg (fun f : TraceClass H →L[ℂ] ℂ => f T) he

end Cloning.WeylSqueezer
