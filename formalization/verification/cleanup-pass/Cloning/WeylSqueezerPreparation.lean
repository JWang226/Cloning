import Cloning.WeylSqueezerProductDisplacement
import Cloning.WeylSqueezerIdlerState
import Cloning.WeylSqueezerKraus

/-! Preparation of an arbitrary correlated mixed idler beside an arbitrary
signal input, as a genuine CPTP channel on the entire trace class. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.WeylSqueezer
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass
open Cloning.WeylSqueezerProduct
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def preparationKraus (σ : DensityState (Fock d)) (i : IdlerIndex d) :
    Fock d →L[ℂ] Fock (d+d) := tensorRight (idlerVector σ i)

theorem preparationKraus_complete (σ : DensityState (Fock d)) :
    RectangularKrausComplete (preparationKraus σ) := by
  intro x
  have hh := (idlerVector_norm_sq_hasSum σ).mul_left (‖x‖^2)
  simpa only [preparationKraus,tensorRight_apply,WeylSqueezerProduct.tensorVector_norm,
    mul_pow,mul_one] using hh

def preparationChannel (σ : DensityState (Fock d)) : QuantumChannel (Fock d) (Fock (d+d)) :=
  QuantumChannel.ofRectangularKraus (preparationKraus σ) (preparationKraus_complete σ)

theorem preparationChannel_pure_hasSum (σ : DensityState (Fock d)) (x : Fock d) :
    HasSum (fun i => vectorProjector (WeylSqueezerProduct.tensorVector x (idlerVector σ i)))
      ((preparationChannel σ).toLinearMap (vectorProjector x)) := by
  have hh := QuantumChannel.ofRectangularKraus_vectorProjector_hasSum
    (preparationKraus σ) (preparationKraus_complete σ) x
  simpa only [preparationKraus,tensorRight_apply] using hh

/-- Exact product characteristic function, with a full mixed idler and every
complex trace-class signal input. -/
theorem preparationChannel_characteristic (σ : DensityState (Fock d))
    (T : TraceClass (Fock d)) (a b : Fin d → ℂ) :
    tracePairing ((preparationChannel σ).toLinearMap T) (displacement (Fin.append a b))=
      tracePairing (idlerTraceClass σ) (displacement b)*tracePairing T (displacement a) := by
  apply channel_pairing_of_pure
  intro x
  have hs := rectangularKraus_pairing_pure_hasSum (preparationKraus σ)
    (preparationKraus_complete σ) x (displacement (Fin.append a b))
  have ht := (idlerVector_pairing_hasSum σ (displacement b)).mul_left
    ⟪x,displacement a x⟫_ℂ
  have he (i : IdlerIndex d) :
      ⟪preparationKraus σ i x,displacement (Fin.append a b) (preparationKraus σ i x)⟫_ℂ=
        ⟪x,displacement a x⟫_ℂ*⟪idlerVector σ i,displacement b (idlerVector σ i)⟫_ℂ := by
    simp only [preparationKraus,tensorRight_apply,displacement_append_tensor,tensorVector_inner]
  simp_rw [he] at hs
  exact hs.unique (by simpa only [mul_comm] using ht)

end Cloning.WeylSqueezer
