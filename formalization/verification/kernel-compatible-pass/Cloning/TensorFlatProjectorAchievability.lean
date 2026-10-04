import Cloning.TensorFlatProjectorChannel

/-! Unconditional flat-projector achievability by an explicit physical CPTP channel. -/
noncomputable section
open scoped BigOperators Classical Matrix Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.InfiniteTraceClass
open Cloning.PCT Cloning.TensorLie Cloning.YoungFlat Cloning.YoungFlatCoupling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The exact physical coupling determines a channel without knowing the eigenbasis. -/
def rankFlatChannel (r k : ℕ) (hr : 0<r) (n m : ℕ) :
    QuantumChannel (TensorRegister n (Fin (r+k))) (TensorRegister m (Fin (r+k))) :=
  flatCoupledChannel k hr (rankFlatCoupling r hr n m)
    (rankFlatCoupling_map_fst r hr n m) (rankFlatCoupling_map_snd r hr n m)

/-- Uniform achievability on the entire rank-r flat-state orbit. -/
theorem eventually_rankFlatChannel_payoff_lower (r k : ℕ) (hr : 0<r)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ => (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, ∀ U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ),
      γ^(-(((r*k : ℕ) : ℝ)/2))-ε <
        PhysicalFlatConverse.payoff r k hr N (m N) (rankFlatChannel r k hr N (m N)) U := by
  have h := rankFlatCoupling_fidelity_tendsto r k hr m hm γ hγ hratio
  filter_upwards [h.eventually (eventually_gt_nhds (show
    γ^(-(((r*k : ℕ) : ℝ)/2))-ε < γ^(-(((r*k : ℕ) : ℝ)/2)) by linarith))] with N hN U
  exact hN.trans_le (flatCoupledChannel_payoff_lower k hr (rankFlatCoupling r hr N (m N))
    (rankFlatCoupling_map_fst r hr N (m N)) (rankFlatCoupling_map_snd r hr N (m N)) U)

/-- The optimization over all actual input-output CPTP maps inherits the sharp lower bound. -/
theorem eventually_rankFlat_minimaxValue_lower (r k : ℕ) (hr : 0<r)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ => (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, γ^(-(((r*k : ℕ) : ℝ)/2))-ε <
      PhysicalFlatConverse.minimaxValue r k hr N (m N) := by
  filter_upwards [eventually_rankFlatChannel_payoff_lower r k hr m hm γ hγ hratio
    (ε/2) (by positivity)] with N hN
  have hh := LAN.candidate_le_minimaxValue (PhysicalFlatConverse.payoff r k hr N (m N))
    (rankFlatChannel r k hr N (m N)) (γ^(-(((r*k : ℕ) : ℝ)/2))-ε/2)
    (PhysicalFlatConverse.payoff_le_one r k hr N (m N)) (fun U => (hN U).le)
    (PhysicalFlatConverse.payoff_nonneg r k hr N (m N))
  change γ^(-(((r*k : ℕ) : ℝ)/2))-ε/2 ≤ PhysicalFlatConverse.minimaxValue r k hr N (m N) at hh
  linarith

end Cloning.TensorCloning
