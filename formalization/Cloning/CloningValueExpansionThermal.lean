import Cloning.CloningValueExpansionAlgebra
import Cloning.Thermal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Exact one-mode quadratic losses with cubic remainders. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.ValueExpansion
open Cloning.Thermal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def thermalLoss (q x : ℝ) : ℝ :=
  (Real.sqrt q-Real.sqrt x)/(1-Real.sqrt q*Real.sqrt x)

theorem fidelity_sq_eq_one_sub_loss_sq {q x : ℝ}
    (hq : 0<q) (hq1 : q<1) (hx : 0<x) (hx1 : x<1) :
    fidelity q x^2=1-thermalLoss q x^2 := by
  have hp : Real.sqrt q*Real.sqrt x<1 := by
    rw [←Real.sqrt_mul hq.le,Real.sqrt_lt' (by norm_num : (0:ℝ)<1)]
    simpa using mul_lt_one_of_nonneg_of_lt_one_right hq1.le hx.le hx1
  rw [fidelity_sq hq.le hq1 hx.le hx1]
  dsimp only [thermalLoss]
  field_simp [ne_of_gt (sub_pos.mpr hp)]
  nlinarith [Real.sq_sqrt hq.le,Real.sq_sqrt hx.le]

theorem thermalLoss_self {q : ℝ} (hq : 0≤q) : thermalLoss q q=0 := by
  simp only [thermalLoss,sub_self,zero_div]

theorem thermalLoss_contDiffAt {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ContDiffAt ℝ 2 (thermalLoss q) q := by
  apply (contDiffAt_const.sub (contDiffAt_id.sqrt hq.ne')).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.sqrt hq.ne')))
  simp only [id_eq]
  rw [←pow_two,Real.sq_sqrt hq.le]
  exact (sub_pos.mpr hq1).ne'

theorem thermalLoss_hasDerivAt {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    HasDerivAt (thermalLoss q) (-(1/(2*Real.sqrt q*(1-q)))) q := by
  have hden : 1-Real.sqrt q*Real.sqrt q≠0 := by
    rw [←pow_two,Real.sq_sqrt hq.le]
    exact (sub_pos.mpr hq1).ne'
  have hs := Real.hasDerivAt_sqrt hq.ne'
  have h := ((hasDerivAt_const q (Real.sqrt q)).sub hs).div
    ((hasDerivAt_const q 1).sub (hs.const_mul (Real.sqrt q))) hden
  convert h using 1
  simp only [Pi.sub_apply,zero_sub,sub_self,zero_mul,sub_zero,←pow_two,Real.sq_sqrt hq.le]
  field_simp [hq.ne',ne_of_gt (Real.sqrt_pos.mpr hq),(sub_pos.mpr hq1).ne']
  <;> ring

theorem thermal_path_expansion {q v : ℝ} {f : ℝ→ℝ}
    (hq : 0<q) (hq1 : q<1) (hf : ContDiffAt ℝ 2 f 0)
    (hf0 : f 0=q) (hd : HasDerivAt f v 0) :
    HasQuadraticExpansion (fun x=>fidelity q (f x)^2)
      (v^2/(4*q*(1-q)^2)) := by
  let a := -(1/(2*Real.sqrt q*(1-q)))*v
  have hOuter : ContDiffAt ℝ 2 (thermalLoss q) (f 0) := by
    rw [hf0]
    exact thermalLoss_contDiffAt hq hq1
  have hC : ContDiffAt ℝ 2 (fun x=>thermalLoss q (f x)) 0 := hOuter.comp 0 hf
  have hzero : thermalLoss q (f 0)=0 := by rw [hf0,thermalLoss_self hq.le]
  have hOuterD : HasDerivAt (thermalLoss q) (-(1/(2*Real.sqrt q*(1-q)))) (f 0) := by
    rw [hf0]
    exact thermalLoss_hasDerivAt hq hq1
  have hD : HasDerivAt (fun x=>thermalLoss q (f x)) a 0 := hOuterD.comp 0 hd
  have hs := (square_zero_remainder hC hzero hD).neg_left
  have ha : a^2=v^2/(4*q*(1-q)^2) := by
    dsimp only [a]
    rw [mul_pow,neg_sq,div_pow]
    simp only [one_pow,mul_pow,Real.sq_sqrt hq.le]
    ring
  have hft : Tendsto f (𝓝 (0:ℝ)) (𝓝 q) := hf0 ▸ hd.continuousAt
  have he : ∀ᶠx in 𝓝 (0:ℝ), 0<f x ∧ f x<1 :=
    hft (Ioo_mem_nhds hq hq1)
  apply hs.congr' ?_ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [he] with x hx
  rw [fidelity_sq_eq_one_sub_loss_sq hq hq1 hx.1 hx.2,←ha]
  ring

theorem amplified_path_hasDerivAt (q : ℝ) :
    HasDerivAt (fun x : ℝ=>amplified (1+x) q) (1-q) 0 := by
  have h := (hasDerivAt_const 0 1).sub
    ((hasDerivAt_const 0 (1-q)).div ((hasDerivAt_id 0).const_add 1) (by norm_num))
  convert h using 1 <;> simp only [amplified,id_eq] <;> ring

theorem amplified_fidelity_expansion {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    HasQuadraticExpansion (fun x=>fidelity q (amplified (1+x) q)^2) (1/(4*q)) := by
  have hc : ContDiffAt ℝ 2 (fun x : ℝ=>amplified (1+x) q) 0 :=
    contDiffAt_const.sub (contDiffAt_const.div (contDiffAt_const.add contDiffAt_id) (by norm_num))
  have h0 : amplified (1+(0:ℝ)) q=q := by simp [amplified]
  convert thermal_path_expansion hq hq1 hc h0 (amplified_path_hasDerivAt q) using 1
  field_simp [(sub_pos.mpr hq1).ne',hq.ne']

theorem pct_path_hasDerivAt (q : ℝ) :
    HasDerivAt (fun x : ℝ=>pct (1+x) q) (1-q^2) 0 := by
  have hid := (hasDerivAt_id (0:ℝ)).const_add 1
  have h := ((hid.sub_const 1).add (hid.mul_const q)).div
    (hid.add ((hid.sub_const 1).mul_const q)) (by norm_num)
  convert h using 1 <;> simp [pct] <;> ring

theorem pct_fidelity_expansion {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    HasQuadraticExpansion (fun x=>fidelity q (pct (1+x) q)^2) ((1+q)^2/(4*q)) := by
  have hc : ContDiffAt ℝ 2 (fun x : ℝ=>pct (1+x) q) 0 := by
    unfold pct
    fun_prop (disch:=norm_num)
  have h0 : pct (1+(0:ℝ)) q=q := by simp [pct]
  convert thermal_path_expansion hq hq1 hc h0 (pct_path_hasDerivAt q) using 1
  field_simp [(sub_pos.mpr hq1).ne',hq.ne']
  <;> ring

end Cloning.ValueExpansion
