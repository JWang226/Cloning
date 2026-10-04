import Cloning.CloningValueExpansionThermal
import Cloning.Main

/-! Classical Gaussian affinity and real powers preserve the exact cubic error. -/
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem HasQuadraticExpansion.rpow {f : ℝ→ℝ} {a : ℝ}
    (hf : HasQuadraticExpansion f a) (c : ℝ) :
    HasQuadraticExpansion (fun x=>f x^c) (c*a) := by
  have hc : ContDiffAt ℝ 2 (fun y : ℝ=>(1+y)^c) 0 :=
    (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by norm_num)
  have hd : HasDerivAt (fun y : ℝ=>(1+y)^c) c 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const (Or.inl (by norm_num)) using 1 <;> simp
  have hr : (fun y : ℝ=>(1+y)^c-(1+c*y)) =O[𝓝 (0:ℝ)] (fun y=>y^2) := by
    have h := ScalarTaylor.local_taylor_isBigO 1 hc
    convert h using 1
    · ext x
      simp only [taylorWithinEval_succ,taylor_within_zero_eval,
        iteratedDerivWithin_univ,iteratedDeriv_one,smul_eq_mul,sub_zero]
      norm_num
      rw [hd.deriv]
      ring
    · simp
  have hu : Tendsto (fun x=>f x-1) (𝓝 0) (𝓝 0) := by
    simpa using hf.tendsto.sub_const 1
  have hu2 : (fun x=>f x-1) =O[𝓝 (0:ℝ)] (fun x=>x^2) := by
    have h := (hf.trans (isLittleO_pow_pow (by decide : 2<3)).isBigO).sub
      (isBigO_const_mul_self a (fun x : ℝ=>x^2) (𝓝 0))
    convert h using 1
    ext x
    ring
  have hu4 : (fun x=>(f x-1)^2) =O[𝓝 (0:ℝ)] (fun x=>x^4) := by
    convert hu2.mul hu2 using 1 <;> ext x <;> ring
  have hcomp := ((hr.comp_tendsto hu).trans hu4).trans
    (isLittleO_pow_pow (by decide : 3<4)).isBigO
  have hh := hcomp.add (hf.const_mul_left c)
  dsimp only [HasQuadraticExpansion] at *
  convert hh using 1
  ext x
  simp only [Function.comp_apply]
  rw [show 1+(f x-1)=f x by ring]
  ring

theorem classicalBase_squared_expansion (c : ℝ) :
    HasQuadraticExpansion (fun x=>Thermal.classicalBase (1+c*x)^2) (c^2/4) := by
  let f : ℝ→ℝ := fun x=>c*x/(2+c*x)
  have hc : ContDiffAt ℝ 2 f 0 := by
    dsimp only [f]
    fun_prop (disch:=norm_num)
  have hzero : f 0=0 := by simp [f]
  have hd : HasDerivAt f (c/2) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).const_mul c).div
      (((hasDerivAt_id (0:ℝ)).const_mul c).const_add 2) (by norm_num)
    convert h using 1 <;> simp only [f,id_eq] <;> ring
  have h := (square_zero_remainder hc hzero hd).neg_left
  have he : ∀ᶠx : ℝ in 𝓝 0,0<1+c*x :=
    (show ContinuousAt (fun x : ℝ=>1+c*x) 0 by fun_prop)
      (Ioi_mem_nhds (by norm_num))
  apply h.congr' ?_ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [he] with x hx
  dsimp only [HasQuadraticExpansion,Thermal.classicalBase,f]
  simp only [div_pow,mul_pow,Real.sq_sqrt hx.le]
  have hd : 2+c*x≠0 := by linarith
  rw [show 1+(1+c*x)=2+c*x by ring]
  field_simp [hd]
  <;> ring

theorem classicalValue_squared_expansion (c : ℝ) (d : ℕ) :
    HasQuadraticExpansion (fun x=>classicalValue (1+c*x) d^2)
      (((d:ℝ)-1)*c^2/8) := by
  have h := (classicalBase_squared_expansion c).rpow (((d:ℝ)-1)/2)
  have he : ∀ᶠx : ℝ in 𝓝 0,0<1+c*x :=
    (show ContinuousAt (fun x : ℝ=>1+c*x) 0 by fun_prop)
      (Ioi_mem_nhds (by norm_num))
  apply h.congr' ?_ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [he] with x hx
  dsimp only [HasQuadraticExpansion,classicalValue]
  have hb := (Thermal.classicalBase_pos hx).le
  rw [pow_two,Real.mul_rpow hb hb,←pow_two]
  congr 1
  ring

end Cloning.ValueExpansion
