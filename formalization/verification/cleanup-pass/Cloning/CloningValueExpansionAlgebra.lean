import Cloning.ScalarTaylorRemainder
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Cubic remainders for squared losses and finite products. -/
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false

/-- Squaring a twice differentiable simple zero keeps a cubic remainder. -/
theorem square_zero_remainder {f : ℝ→ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hzero : f 0=0) (hd : HasDerivAt f a 0) :
    (fun x=>f x^2-a^2*x^2) =O[𝓝 (0:ℝ)] (fun x=>x^3) := by
  have hr : (fun x=>f x-a*x) =O[𝓝 (0:ℝ)] (fun x=>x^2) := by
    have h := ScalarTaylor.local_taylor_isBigO 1 hf
    convert h using 1
    · ext x
      simp only [taylorWithinEval_succ,taylor_within_zero_eval,
        iteratedDerivWithin_univ,iteratedDeriv_one,smul_eq_mul,hzero,sub_zero]
      norm_num
      rw [hd.deriv]
      ring
    · simp
  have hf1 : f =O[𝓝 (0:ℝ)] (fun x=>x) := by
    simpa only [hzero,sub_zero] using hd.isBigO_sub
  have hs := hr.mul (hf1.add (isBigO_const_mul_self a (fun x : ℝ=>x) (𝓝 0)))
  convert hs using 1 <;> ext x <;> ring

def HasQuadraticExpansion (f : ℝ→ℝ) (a : ℝ) : Prop :=
  (fun x=>f x-(1-a*x^2)) =O[𝓝 (0:ℝ)] (fun x=>x^3)

theorem HasQuadraticExpansion.one : HasQuadraticExpansion (fun _=>1) 0 := by
  simpa only [HasQuadraticExpansion,zero_mul,sub_zero,sub_self] using
    (isBigO_zero (fun x : ℝ=>x^3) (𝓝 (0:ℝ)))

theorem HasQuadraticExpansion.tendsto {f : ℝ→ℝ} {a : ℝ}
    (hf : HasQuadraticExpansion f a) : Tendsto f (𝓝 0) (𝓝 1) := by
  have hr : Tendsto (fun x=>f x-(1-a*x^2)) (𝓝 (0:ℝ)) (𝓝 0) :=
    hf.trans_tendsto (by simpa using (tendsto_id.pow 3 : Tendsto (fun x : ℝ=>x^3) (𝓝 0) (𝓝 (0^3))))
  have hp : Tendsto (fun x : ℝ=>1-a*x^2) (𝓝 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(1:ℝ)) (𝓝 0) (𝓝 1)).sub
      (((tendsto_id : Tendsto (fun x : ℝ=>x) (𝓝 0) (𝓝 0)).pow 2).const_mul a)
  convert hr.add hp using 1 <;> simp

theorem HasQuadraticExpansion.mul {f g : ℝ→ℝ} {a b : ℝ}
    (hf : HasQuadraticExpansion f a) (hg : HasQuadraticExpansion g b) :
    HasQuadraticExpansion (fun x=>f x*g x) (a+b) := by
  have hp : Tendsto (fun x : ℝ=>1-a*x^2) (𝓝 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(1:ℝ)) (𝓝 0) (𝓝 1)).sub
      (((tendsto_id : Tendsto (fun x : ℝ=>x) (𝓝 0) (𝓝 0)).pow 2).const_mul a)
  have h₁ := Asymptotics.IsBigO.mul hf (hg.tendsto.isBigO_one ℝ)
  have h₂ := Asymptotics.IsBigO.mul (hp.isBigO_one ℝ) hg
  simp only [mul_one,one_mul] at h₁ h₂
  have h₃ := ((isLittleO_pow_pow (by decide : 3<4) (𝕜:=ℝ)).isBigO).const_mul_left (a*b)
  have h := (h₁.add h₂).add h₃
  dsimp only [HasQuadraticExpansion] at *
  convert h using 1 <;> ext x <;> ring

theorem HasQuadraticExpansion.prod {ι : Type*} (s : Finset ι)
    (f : ι→ℝ→ℝ) (a : ι→ℝ) (h : ∀i∈s,HasQuadraticExpansion (f i) (a i)) :
    HasQuadraticExpansion (fun x=>∏i∈s,f i x) (∑i∈s,a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using HasQuadraticExpansion.one
  | @insert i s his ih =>
    simpa only [Finset.prod_insert his,Finset.sum_insert his] using
      (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))

end Cloning.ValueExpansion
