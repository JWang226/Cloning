import Cloning.SampleRatioExpansion

/-! The leading sample-ratio asymptotic from the exact threshold. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.SampleRatio

theorem threshold_scaled_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun ε => ε*threshold a ε) (𝓝[≠] (0:ℝ)) (𝓝 a) := by
  have hf : HasDerivAt (fun x : ℝ => (1-x)^(-1/a)-1) (1/a) 0 := by
    have hh := (ScalarTaylor.hasDerivAt_one_sub_rpow (-1/a) 0 (by norm_num)).sub_const 1
    convert hh using 1 <;> simp [div_eq_mul_inv]
  have hq : Tendsto (fun x : ℝ => ((1-x)^(-1/a)-1)/x) (𝓝[≠] (0:ℝ)) (𝓝 (1/a)) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using hf.tendsto_slope_zero
  have hh := hq.inv₀ (one_div_ne_zero ha.ne')
  simpa [threshold,div_eq_mul_inv,mul_comm] using hh

theorem threshold_relative_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun ε => threshold a ε/(a/ε)) (𝓝[≠] (0:ℝ)) (𝓝 (1:ℝ)) := by
  have hh := (threshold_scaled_tendsto ha).div_const a
  simpa [div_eq_mul_inv,ha.ne',mul_comm,mul_left_comm,mul_assoc] using hh

end Cloning.SampleRatio
