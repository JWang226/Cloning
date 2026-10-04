import Cloning.PCTPrescribedRank
import Cloning.PhysicalFlatPCTTheorem

/-! The rank-adapted PCT comparison for arbitrary requested output sizes,
using one fixed physical channel for every literal Grassmann projector. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PCTPrescribed
open Cloning.PCT Cloning.TensorLie Cloning.TensorCloning Cloning.InfiniteTraceClass
open Cloning.PCTPhysicalState Cloning.PhysicalFlatGrassmann Cloning.PCTRankAdapted
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance rankTheoremAmbientNonempty (d k : ℕ) : Nonempty (Fin (d+1+k)) := ⟨⟨0,by omega⟩⟩

theorem rankFidelity_of_le (d k : ℕ) (P : Projector (d+1) k) (n m : ℕ) (h : m≤n) :
    rankFidelity d k P n m=1 :=
  extendChannel_payoff_of_le (PhysicalFlatPCT.channel d k) n m h (state (by omega : 0<d+1) P)

/-- The exact manuscript bound holds for arbitrary m(n)/n→γ>1. -/
theorem rankFidelity_limsup_le (d k : ℕ) (P : Projector (d+1) k)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => rankFidelity d k P n (m n)) atTop ≤
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) *
        (Real.sqrt (2*γ-1)/γ) ^ ((((d+1 : ℕ) : ℝ)-1)/2) := by
  rw [← limsup_congr (eventually_rankFidelity d k P m hγ hgain)]
  exact PhysicalFlatPCT.fidelity_limsup_le d k P (fun n => m n-n) γ hγ (addedCopies_ratio m hγ hgain)

theorem rankFidelity_limsup_lt_optimal (d k : ℕ) (hd : 0<d) (P : Projector (d+1) k)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => rankFidelity d k P n (m n)) atTop <
      γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) :=
  (rankFidelity_limsup_le d k P m γ hγ hgain).trans_lt
    (rankAdaptedBound_lt_optimal hγ (by omega : 1<d+1) k)

/-- One sample threshold works for all unknown projectors. -/
theorem rankFidelity_uniform_upper (d k : ℕ) (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ P : Projector (d+1) k,
      rankFidelity d k P n (m n) <
        γ ^ (-((((d+1)*k : ℕ) : ℝ)/2)) *
          (Real.sqrt (2*γ-1)/γ) ^ ((((d+1 : ℕ) : ℝ)-1)/2)+ε := by
  have h := PhysicalFlatPCT.fidelity_uniform_upper d k (fun n => m n-n) γ hγ
    (addedCopies_ratio m hγ hgain) ε hε
  filter_upwards [h,eventually_output_gt_input m hγ hgain] with n hn hnm P
  have he := extendChannel_payoff_of_gt (PhysicalFlatPCT.channel d k) n (m n) hnm
    (state (by omega : 0<d+1) P)
  change rankFidelity d k P n (m n)=PhysicalFlatPCT.fidelity d k P n (m n-n) at he
  rw [he]
  exact hn P

end Cloning.PCTPrescribed
