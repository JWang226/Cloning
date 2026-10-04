import Cloning.SampleRatioThreshold
import Cloning.ScalarTaylorInverse
import Cloning.ScalarPowerExpansion

/-! The first two terms of the exact inverse power-fidelity threshold,
with the manuscript's O(error) remainder. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.SampleRatio
set_option backward.isDefEq.respectTransparency false

theorem threshold_expansion {a : ℝ} (ha : 0<a) :
    (fun ε => threshold a ε-(a/ε-(a+1)/2))
      =O[𝓝[≠] (0:ℝ)] (fun ε => ε) := by
  let f : ℝ → ℝ := fun x => (1-x)^(-1/a)-1
  let α : ℝ := 1/a
  let β : ℝ := (a+1)/(2*a^2)
  have hα : α≠0 := one_div_ne_zero ha.ne'
  have hf0 : f 0=0 := by simp [f]
  have hf : HasDerivAt f α 0 := by
    have hh := (ScalarTaylor.hasDerivAt_one_sub_rpow (-1/a) 0 (by norm_num)).sub_const 1
    convert hh using 1 <;> simp [f,α,div_eq_mul_inv]
  have hrem : (fun x => f x-α*x-β*x^2) =O[𝓝 (0:ℝ)] (fun x => x^3) := by
    have hh := ScalarTaylor.one_sub_rpow_quadratic (-1/a)
    convert hh using 1
    ext x
    dsimp [f,α,β]
    field_simp
    <;> ring
  have hi := ScalarTaylor.inverse_remainder hα hf0 hf hrem
  apply hi.congr' ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x≠0 := hx
  have he₁ : (α*x)⁻¹=a/x := by simp [α, mul_inv, div_eq_mul_inv,mul_comm]
  have he₂ : β/α^2=(a+1)/2 := by
    dsimp [α,β]
    field_simp
  rw [he₁,he₂]
  dsimp [f,threshold]
  ring

end Cloning.SampleRatio
