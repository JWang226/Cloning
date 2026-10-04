import Cloning.Thermal
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The two-scale crossover to the pure-state loss. Unlike fixed-spectrum
Taylor expansions, the mode ratio is allowed to approach zero faster than
the positive gain increment. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.Thermal
set_option maxHeartbeats 500000

private theorem scaled_root_tendsto {q : ℝ→ℝ}
    (hq0 : ∀ᶠ δ in 𝓝[>] (0:ℝ),0≤q δ)
    (hq : q =o[𝓝[>] (0:ℝ)] (fun δ=>δ)) :
    Tendsto (fun δ=>Real.sqrt (q δ*(δ+q δ))/δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hr := hq.tendsto_div_nhds_zero
  have h := (hr.mul (hr.const_add 1)).sqrt
  simp only [zero_mul,Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [hq0,self_mem_nhdsWithin] with δ hqδ hδ
  have hδ0 : 0<δ := hδ
  symm
  calc
    Real.sqrt (q δ*(δ+q δ))/δ = Real.sqrt (q δ*(δ+q δ)/δ^2) := by
      rw [Real.sqrt_div (mul_nonneg hqδ (by linarith)),Real.sqrt_sq hδ0.le]
    _ = _ := by congr 1; field_simp <;> ring

/-- In the regime q=o(δ), the squared one-mode factor agrees with pure-state
squared fidelity up to o(δ). Nonnegativity is only required eventually. -/
theorem modeFactor_near_pure {q : ℝ→ℝ}
    (hq0 : ∀ᶠ δ in 𝓝[>] (0:ℝ),0≤q δ)
    (hq : q =o[𝓝[>] (0:ℝ)] (fun δ=>δ)) :
    (fun δ=>modeFactor (1+δ) (q δ)^2-(1+δ)⁻¹)
      =o[𝓝[>] (0:ℝ)] (fun δ=>δ) := by
  have hid : Tendsto (fun δ:ℝ=>δ) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hqz := hq.tendsto_zero_of_tendsto hid
  have hr := hq.tendsto_div_nhds_zero
  have hg : Tendsto (fun δ:ℝ=>1+δ) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using hid.const_add 1
  have hs := scaled_root_tendsto hq0 hq
  have hb : Tendsto (fun δ:ℝ=>Real.sqrt (1+δ)/(1+δ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using hg.sqrt.div hg (by norm_num : (1:ℝ)≠0)
  have hm : Tendsto (fun δ=>modeFactor (1+δ) (q δ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h := (modeFactor_continuousAt (g:=1) (q:=0) (by norm_num)).tendsto.comp (hg.prodMk_nhds hqz)
    simpa [modeFactor,Function.comp_def] using h
  have hd := ((hg.mul hs).sub (hg.sqrt.mul hr)).div (hg.mul (hg.add hqz)) (by norm_num : (1:ℝ)*(1+0)≠0)
  simp only [one_mul,mul_zero,sub_zero,zero_div] at hd
  have hd' : Tendsto (fun δ=>(modeFactor (1+δ) (q δ)-Real.sqrt (1+δ)/(1+δ))/δ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply hd.congr'
    filter_upwards [hq0,self_mem_nhdsWithin] with δ hqδ hδ
    have hδ0 : 0<δ := hδ
    have hg0 : 0<1+δ := by linarith
    have hden : 0<1+δ+q δ := by linarith
    dsimp only [modeFactor,Pi.div_apply]
    have he : 1+δ-1+q δ=δ+q δ := by ring
    rw [he]
    field_simp [hδ0.ne',hg0.ne',hden.ne']
    <;> ring
  have hsq := hd'.mul (hm.add hb)
  simp only [zero_mul] at hsq
  apply isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ hzero
    exact False.elim ((ne_of_gt hδ) hzero)
  · apply hsq.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : 0<δ := hδ
    have hg0 : 0<1+δ := by linarith
    have hsquare : (Real.sqrt (1+δ)/(1+δ))^2=(1+δ)⁻¹ := by
      rw [div_pow,Real.sq_sqrt hg0.le]
      field_simp
    rw [←hsquare]
    ring

/-- The pair contributes first-order squared infidelity with coefficient one. -/
theorem modeFactor_near_pure_infidelity {q : ℝ→ℝ}
    (hq0 : ∀ᶠ δ in 𝓝[>] (0:ℝ),0≤q δ)
    (hq : q =o[𝓝[>] (0:ℝ)] (fun δ=>δ)) :
    Tendsto (fun δ=>(1-modeFactor (1+δ) (q δ)^2)/δ)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hid : Tendsto (fun δ:ℝ=>δ) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hg : Tendsto (fun δ:ℝ=>(1+δ)⁻¹) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using (hid.const_add 1).inv₀ (by norm_num : (1+(0:ℝ))≠0)
  have h := hg.sub (modeFactor_near_pure hq0 hq).tendsto_div_nhds_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0<δ := hδ
  have hg0 : 0<1+δ := by linarith
  field_simp [hδ0.ne',hg0.ne']
  <;> ring

end Cloning.Thermal
