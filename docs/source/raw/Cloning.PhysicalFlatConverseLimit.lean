import Cloning.PhysicalFlatConverseFinite

/-! The sharp asymptotic upper bound for every physical cloning channel on
the rank-flat orbit. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PhysicalFlatConverse

theorem eventually_minimaxValue_upper (r k : ℕ) (hr : 0<r)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 0<γ)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, minimaxValue r k hr n (m n) < γ^(-(((r*k : ℕ) : ℝ)/2))+ε := by
  have h := flatConverseBound_tendsto r k hr m hm γ hγ hratio
  filter_upwards [h.eventually (eventually_lt_nhds (show
    γ^(-(((r*k : ℕ) : ℝ)/2)) < γ^(-(((r*k : ℕ) : ℝ)/2))+ε by linarith))] with n hn
  exact (minimaxValue_le_flatConverseBound r k hr n (m n)).trans_lt hn

end Cloning.PhysicalFlatConverse
