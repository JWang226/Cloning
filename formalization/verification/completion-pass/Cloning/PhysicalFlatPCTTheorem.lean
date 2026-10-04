import Cloning.PhysicalFlatPCTAction
import Cloning.PhysicalFlatPCTBound

/-! The rank-adapted physical PCT theorem for one fixed all-input CPTP
channel and every literal Grassmann projector, with a strict optimality gap. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.PhysicalFlatPCT
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted
open Cloning.PhysicalFlatGrassmann Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance theoremAmbientNeZero (d k : ℕ) : NeZero (d+1+k) := ⟨by omega⟩

/-- Exact finite-sample fidelity, independent of the unknown projector. -/
theorem fidelity_eq_supportFactor (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) :
    fidelity d k P n t =
      Real.sqrt (supportFactor n (n+t) (d*(d+2)) (flatPurificationDimension d k)) *
        (PCTPhysicalState.outputState (flat_internal_register_card d) (flatInternalState d) n t).rootFidelity
          (tensorState (flatInternalState d) (n+t)) := by
  obtain ⟨J,hJ,hP⟩ := exists_embedded_flatState d k P
  unfold fidelity
  rw [outputState_eq_flatEmbeddedOutput d k P J hJ hP, hP]
  exact embeddedPurificationOutput_fidelity_factorization
    (flat_internal_register_card d) (flat_ambient_register_card d k) J hJ (flatInternalState d) n t

/-- Theorem (b), for the actual fixed PCT channel and a literal rank-(d+1)
projector in ambient dimension d+1+k. No action, Gaussian, or limit premise is supplied. -/
theorem fidelity_limsup_le (d k : ℕ) (P : Projector (d+1) k)
    (t : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => fidelity d k P n (t n)) atTop ≤
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) *
        (Real.sqrt (2*γ-1)/γ) ^ ((((d+1 : ℕ) : ℝ)-1)/2) := by
  obtain ⟨J,hJ,hP⟩ := exists_embedded_flatState d k P
  have he : (fun n => fidelity d k P n (t n)) =
      (fun n => (flatEmbeddedOutput d k J hJ n (t n)).rootFidelity
        (tensorState (embeddedState J hJ (flatInternalState d)) (n+t n))) := by
    funext n
    unfold fidelity
    rw [outputState_eq_flatEmbeddedOutput d k P J hJ hP, hP]
  rw [he]
  exact flatEmbeddedOutput_limsup_le d k J hJ t γ hγ hgain

/-- Supported rank greater than one gives a strict gap below the sharp
Grassmann minimax value. -/
theorem fidelity_limsup_lt_optimal (d k : ℕ) (hd : 0<d) (P : Projector (d+1) k)
    (t : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => fidelity d k P n (t n)) atTop <
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) :=
  (fidelity_limsup_le d k P t γ hγ hgain).trans_lt
    (rankAdaptedBound_lt_optimal hγ (by omega : 1<d+1) k)

/-- The upper estimate is uniform over all projectors for the same fixed
channel sequence; the sample cutoff is selected before the projector. -/
theorem fidelity_uniform_upper (d k : ℕ) (t : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ P : Projector (d+1) k,
      fidelity d k P n (t n) <
        γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) *
          (Real.sqrt (2*γ-1)/γ) ^ ((((d+1 : ℕ) : ℝ)-1)/2)+ε := by
  let P₀ := orbitProjector (d+1) k 1
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => fidelity d k P₀ n (t n)) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => fidelity_le_one d k P₀ n (t n)))
  have h := eventually_lt_of_limsup_lt
    ((fidelity_limsup_le d k P₀ t γ hγ hgain).trans_lt (lt_add_of_pos_right _ hε)) hb
  filter_upwards [h] with n hn P
  simpa only [fidelity_eq_supportFactor] using hn

end Cloning.PhysicalFlatPCT
