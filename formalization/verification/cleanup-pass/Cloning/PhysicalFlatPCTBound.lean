import Cloning.PCTRankAdaptedFlat
import Cloning.PCTCountPhysical

/-! The physical rank-adapted purification--Werner--trace output satisfies
the manuscript's strict suboptimality bound, with no analytic premise. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPhysicalState Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
local instance (d k : ℕ) : Nonempty (Fin (d+1+k)) := ⟨⟨0,by omega⟩⟩

theorem flatInternal_fidelity_eventually_le (d : ℕ) (t : ℕ → ℕ)
    (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (outputState (flat_internal_register_card d) (flatInternalState d) n (t n)).rootFidelity
        (tensorState (flatInternalState d) (n+t n)) ≤ Cloning.classicalValue (2*γ-1) (d+1)+ε := by
  by_cases hd : d=0
  · subst d
    intro ε hε
    apply Eventually.of_forall
    intro n
    have h := internal_fidelity_le_one (flat_internal_register_card 0) (flatInternalState 0) n (t n)
    simpa only [zero_add, Cloning.classicalValue, Nat.cast_one, sub_self, zero_div, Real.rpow_zero]
      using h.trans (le_add_of_nonneg_right hε.le)
  · exact Cloning.PCTCount.internal_flat_fidelity_eventually_le d (d*(d+2))
      (by
        have hdpos : 1≤d := by omega
        nlinarith) (flat_internal_register_card d) t γ hγ hratio

/-- Exact theorem-(b) scalar upper bound on the actual smaller-environment
PCT output. The finite state-independent implementation is supplied by
`PCTRankGlobal.channel`. -/
theorem flatEmbeddedOutput_limsup_le (d k : ℕ)
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1)
    (t : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => (flatEmbeddedOutput d k J hJ n (t n)).rootFidelity
      (tensorState (embeddedState J hJ (flatInternalState d)) (n+t n))) atTop ≤
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) *
        (Real.sqrt (2*γ-1)/γ) ^ ((((d+1 : ℕ) : ℝ)-1)/2) :=
  flatEmbeddedOutput_limsup_of_internal_bound d k J hJ t γ hγ hr
    (flatInternal_fidelity_eventually_le d t γ hγ hr)

/-- For supported rank greater than one the PCT fidelity is strictly below
the sharp Grassmann cloning value. -/
theorem flatEmbeddedOutput_limsup_lt_optimal (d k : ℕ) (hd : 0<d)
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1)
    (t : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => (flatEmbeddedOutput d k J hJ n (t n)).rootFidelity
      (tensorState (embeddedState J hJ (flatInternalState d)) (n+t n))) atTop <
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) :=
  (flatEmbeddedOutput_limsup_le d k J hJ t γ hγ hr).trans_lt
    (rankAdaptedBound_lt_optimal hγ (by omega : 1<d+1) k)

end Cloning.PCTRankAdapted
