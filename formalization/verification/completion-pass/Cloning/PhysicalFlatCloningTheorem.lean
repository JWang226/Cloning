import Cloning.PhysicalFlatConverseLimit
import Cloning.TensorFlatProjectorAchievability

/-! Exact asymptotic cloning fidelity for the literal rank-flat physical
orbit, optimized over all actual quantum channels. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PhysicalFlatConverse

/-- The sharp physical minimax value for rank-r projectors in dimension r+k.
The upper bound applies to all channels; the lower bound uses an explicitly
constructed channel with the exact physical Young marginals. -/
theorem minimaxValue_tendsto (r k : ℕ) (hr : 0<r)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun n => minimaxValue r k hr n (m n)) atTop
      (𝓝 (γ^(-(((r*k : ℕ) : ℝ)/2)))) := by
  have hm : Tendsto m atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    have h := hratio.pos_mul_atTop (lt_trans zero_lt_one hγ)
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact div_mul_cancel₀ (m n : ℝ) (Nat.cast_ne_zero.mpr hn.ne')
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hl := TensorCloning.eventually_rankFlat_minimaxValue_lower r k hr m hm γ hγ hratio ε hε
  have hu := eventually_minimaxValue_upper r k hr m hm γ (lt_trans zero_lt_one hγ) hratio ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hl.and hu)
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq,abs_lt]
  have h := hN n hn
  constructor <;> linarith [h.1,h.2]

end Cloning.PhysicalFlatConverse
