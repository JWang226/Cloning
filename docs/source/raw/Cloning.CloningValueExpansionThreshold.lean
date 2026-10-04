import Cloning.CloningValueExpansion

/-! Leading squared-infidelity coefficients and inversion along every genuine
small-error target branch. The statement keeps the iterated fixed-spectrum
limit separate from finite-sample errors. -/
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem infidelity_div_sq_tendsto {f : ℝ→ℝ} {a : ℝ}
    (h : (fun x=>f x-(1-a*x^2)) =O[𝓝[>] (0:ℝ)] (fun x=>x^3)) :
    Tendsto (fun x=>(1-f x)/x^2) (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have hh := (h.trans_isLittleO
    ((isLittleO_pow_pow (by decide : 2<3) (𝕜:=ℝ)).mono nhdsWithin_le_nhds)).tendsto_div_nhds_zero
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ=>a) (𝓝[>] (0:ℝ)) (𝓝 a)).sub hh
  simp only [sub_zero] at ht
  apply ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x≠0 := ne_of_gt hx
  field_simp [hx0]
  <;> ring

theorem universal_infidelity_div_sq_tendsto {d : ℕ} (p : SimpleSpectrum d) :
    Tendsto (fun x=>(1-universalValue (1+x) p^2)/x^2)
      (𝓝[>] (0:ℝ)) (𝓝 (universalCoefficient p)) :=
  infidelity_div_sq_tendsto (universal_squared_remainder p)

theorem known_infidelity_div_sq_tendsto {d : ℕ} (p : SimpleSpectrum d) :
    Tendsto (fun x=>(1-orbitalValue (1+x) p^2)/x^2)
      (𝓝[>] (0:ℝ)) (𝓝 (knownCoefficient p)) :=
  infidelity_div_sq_tendsto (orbital_squared_remainder p)

theorem pct_infidelity_div_sq_tendsto {d : ℕ} (p : SimpleSpectrum d) :
    Tendsto (fun x=>(1-pctValue (1+x) p^2)/x^2)
      (𝓝[>] (0:ℝ)) (𝓝 (pctCoefficient p)) :=
  infidelity_div_sq_tendsto ((pct_squared_remainder p).mono nhdsWithin_le_nhds)

theorem universalCoefficient_pos {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d) :
    0<universalCoefficient p := by
  have hs : 0≤knownCoefficient p := Finset.sum_nonneg (fun ij _=>by
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (p.ratio_pos ij).le))
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  dsimp only [universalCoefficient]
  linarith

theorem pctCoefficient_pos {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d) :
    0<pctCoefficient p :=
  (universalCoefficient_pos hd p).trans (universalCoefficient_lt_pctCoefficient hd p)

/-- Any positive small-error branch attaining the actual scalar target has
the asserted inverse square-root leading sample ratio. -/
theorem inverse_target_branch_tendsto {f delta : ℝ→ℝ} {a : ℝ} (ha : 0<a)
    (hlim : Tendsto (fun x=>(1-f x)/x^2) (𝓝[>] (0:ℝ)) (𝓝 a))
    (hd : Tendsto delta (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)))
    (htarget : ∀ᶠε in 𝓝[>] (0:ℝ), f (delta ε)=1-ε) :
    Tendsto (fun ε=>(delta ε)⁻¹/Real.sqrt (a/ε)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hr : Tendsto (fun ε=>ε/(delta ε)^2) (𝓝[>] (0:ℝ)) (𝓝 a) := by
    apply (hlim.comp hd).congr'
    filter_upwards [htarget] with ε hε
    simp only [Function.comp_apply,hε,sub_sub_cancel]
  have hs := hr.sqrt.div_const (Real.sqrt a)
  rw [div_self (ne_of_gt (Real.sqrt_pos.mpr ha))] at hs
  apply hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin,hd.eventually self_mem_nhdsWithin] with ε hε hδ
  have hε0 : 0<ε := hε
  have hδ0 : 0<delta ε := hδ
  rw [Real.sqrt_div hε0.le,Real.sqrt_sq hδ0.le,Real.sqrt_div ha.le]
  field_simp [hδ0.ne',ne_of_gt (Real.sqrt_pos.mpr hε0),ne_of_gt (Real.sqrt_pos.mpr ha)]

theorem universal_inverse_target_branch {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d)
    (delta : ℝ→ℝ) (hdelta : Tendsto delta (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)))
    (htarget : ∀ᶠε in 𝓝[>] (0:ℝ),universalValue (1+delta ε) p^2=1-ε) :
    Tendsto (fun ε=>(delta ε)⁻¹/Real.sqrt (universalCoefficient p/ε))
      (𝓝[>] (0:ℝ)) (𝓝 1) :=
  inverse_target_branch_tendsto (universalCoefficient_pos hd p)
    (universal_infidelity_div_sq_tendsto p) hdelta htarget

theorem pct_inverse_target_branch {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d)
    (delta : ℝ→ℝ) (hdelta : Tendsto delta (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)))
    (htarget : ∀ᶠε in 𝓝[>] (0:ℝ),pctValue (1+delta ε) p^2=1-ε) :
    Tendsto (fun ε=>(delta ε)⁻¹/Real.sqrt (pctCoefficient p/ε))
      (𝓝[>] (0:ℝ)) (𝓝 1) :=
  inverse_target_branch_tendsto (pctCoefficient_pos hd p)
    (pct_infidelity_div_sq_tendsto p) hdelta htarget

end Cloning.ValueExpansion
