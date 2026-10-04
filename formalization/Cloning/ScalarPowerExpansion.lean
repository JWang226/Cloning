import Cloning.ScalarTaylorRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The local real-power expansion used in the sample-ratio thresholds. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.ScalarTaylor
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_one_sub_rpow (c x : ℝ) (hx : x<1) :
    HasDerivAt (fun y : ℝ => (1-y)^c) (-c*(1-x)^(c-1)) x := by
  convert ((hasDerivAt_id x).const_sub 1).rpow_const
    (Or.inl (by linarith : 1-x≠0)) using 1 <;> simp only [id_eq] <;> ring

theorem deriv_one_sub_rpow (c x : ℝ) (hx : x<1) :
    deriv (fun y : ℝ => (1-y)^c) x = -c*(1-x)^(c-1) :=
  (hasDerivAt_one_sub_rpow c x hx).deriv

theorem secondDeriv_one_sub_rpow_zero (c : ℝ) :
    deriv (deriv (fun y : ℝ => (1-y)^c)) 0 = c*(c-1) := by
  have he : deriv (fun y : ℝ => (1-y)^c) =ᶠ[𝓝 (0:ℝ)]
      (fun x => -c*(1-x)^(c-1)) := by
    filter_upwards [gt_mem_nhds (show (0:ℝ)<1 by norm_num)] with x hx
    exact deriv_one_sub_rpow c x hx
  rw [he.deriv_eq]
  have hh := (hasDerivAt_one_sub_rpow (c-1) 0 (by norm_num)).const_mul (-c)
  convert hh.deriv using 1 <;> simp <;> ring

theorem one_sub_rpow_quadratic (c : ℝ) :
    (fun x : ℝ => (1-x)^c-(1-c*x+c*(c-1)/2*x^2))
      =O[𝓝 (0:ℝ)] (fun x => x^3) := by
  have hc : ContDiffAt ℝ 3 (fun x : ℝ => (1-x)^c) 0 :=
    (contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (by norm_num)
  have h := quadratic_remainder hc
  rw [secondDeriv_one_sub_rpow_zero, deriv_one_sub_rpow c 0 (by norm_num)] at h
  convert h using 1
  ext x
  simp
  ring

end Cloning.ScalarTaylor
