import Cloning.HeisenbergDual
import Cloning.MultimodeCoherent

/-! A genuine arbitrary mixed idler is resolved into square-root vectors.
The exact trace-norm series and its Weyl expectations are derived from the
positive trace-class operator, without a diagonal-state premise. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def IdlerIndex (d : ℕ) : Set (Fock d) := (exists_hilbertBasis ℂ (Fock d)).choose

def idlerBasis (d : ℕ) : HilbertBasis (IdlerIndex d) ℂ (Fock d) :=
  (exists_hilbertBasis ℂ (Fock d)).choose_spec.choose

def idlerVector (σ : DensityState (Fock d)) (i : IdlerIndex d) : Fock d :=
  CFC.sqrt σ.op (idlerBasis d i)

def idlerTraceClass (σ : DensityState (Fock d)) : TraceClass (Fock d) :=
  TraceClass.ofOperator σ.op σ.traceClass

theorem idlerVector_projector_hasSum (σ : DensityState (Fock d)) :
    HasSum (fun i => vectorProjector (idlerVector σ i)) (idlerTraceClass σ) :=
  positive_rankOne_series σ.positive σ.traceClass (idlerBasis d)

theorem idlerVector_norm_sq_hasSum (σ : DensityState (Fock d)) :
    HasSum (fun i => ‖idlerVector σ i‖^2) 1 := by
  have hh := positive_rankOne_mass σ.positive σ.traceClass (idlerBasis d)
  simpa only [norm_vectorProjector, σ.trace_one, Complex.one_re] using hh

theorem idlerVector_pairing_hasSum (σ : DensityState (Fock d)) (A : Fock d →L[ℂ] Fock d) :
    HasSum (fun i => ⟪idlerVector σ i,A (idlerVector σ i)⟫_ℂ)
      (tracePairing (idlerTraceClass σ) A) := by
  have hh := (idlerVector_projector_hasSum σ).mapL
    ((ContinuousLinearMap.apply ℂ ℂ A).comp tracePairingCLM)
  change HasSum (fun i => tracePairing (vectorProjector (idlerVector σ i)) A)
    (tracePairing (idlerTraceClass σ) A) at hh
  have he (i : IdlerIndex d) : tracePairing (vectorProjector (idlerVector σ i)) A=
      ⟪idlerVector σ i,A (idlerVector σ i)⟫_ℂ :=
    tracePairing_rankOneOperator _ _ A
  simpa only [he] using hh

end Cloning.WeylSqueezer
