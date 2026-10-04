import Cloning.PCTRankAdaptedUpper
import Cloning.YoungGeneralMoments

/-! Canonical dimension bookkeeping for the actual rank-flat PCT output.
The ancilla has the supported rank, while the physical system can be larger. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder
open Filter
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPhysicalState Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- The literal maximally mixed state on the supported rank d+1. -/
def flatInternalState (d : ℕ) : Cloning.MatrixFidelity.State (Fin (d+1)) :=
  diagonalState (Cloning.YoungGeneral.flatSpectrum (d+1))
    (fun _ => by unfold Cloning.YoungGeneral.flatSpectrum; positivity)
    (Cloning.YoungGeneral.flatSpectrum_sum (d+1) (by omega))

def flatPurificationDimension (d k : ℕ) : ℕ := d*(d+2)+k*(d+1)

theorem flat_internal_register_card (d : ℕ) :
    Fintype.card (Fin (d+1) × Fin (d+1)) = d*(d+2)+1 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem flat_ambient_register_card (d k : ℕ) :
    Fintype.card (Fin (d+1+k) × Fin (d+1)) = flatPurificationDimension d k+1 := by
  simp only [Fintype.card_prod, Fintype.card_fin, flatPurificationDimension]
  ring

local instance (d k : ℕ) : Nonempty (Fin (d+1+k)) := ⟨⟨0,by omega⟩⟩

/-- The actual smaller-environment purification--Werner--trace output. -/
def flatEmbeddedOutput (d k : ℕ)
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1) (n t : ℕ) :
    PositiveTraceClass (Register (Fin (n+t) → Fin (d+1+k))) :=
  embeddedPurificationOutput (flat_ambient_register_card d k) J hJ (flatInternalState d) n t

theorem flatEmbeddedOutput_limsup_of_internal_bound (d k : ℕ)
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1)
    (t : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ))
    (hint : ∀ ε > 0, ∀ᶠ n in atTop,
      (outputState (flat_internal_register_card d) (flatInternalState d) n (t n)).rootFidelity
        (tensorState (flatInternalState d) (n+t n)) ≤ Cloning.classicalValue (2*γ-1) (d+1)+ε) :
    limsup (fun n => (flatEmbeddedOutput d k J hJ n (t n)).rootFidelity
      (tensorState (embeddedState J hJ (flatInternalState d)) (n+t n))) atTop ≤
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) *
        (Real.sqrt (2*γ-1)/γ) ^ ((((d+1 : ℕ) : ℝ)-1)/2) := by
  have he : (flatPurificationDimension d k : ℝ) - ((d*(d+2) : ℕ) : ℝ) =
      (((d+1)*k : ℕ) : ℝ) := by
    unfold flatPurificationDimension
    push_cast
    ring
  have h := embeddedPurificationOutput_limsup_of_eventually_upper
    (flat_internal_register_card d) (flat_ambient_register_card d k) J hJ
    (flatInternalState d) t γ hγ hr (Cloning.classicalValue (2*γ-1) (d+1)) hint
  simpa only [flatEmbeddedOutput, he, classicalValue_inflated, neg_div] using h

end Cloning.PCTRankAdapted
