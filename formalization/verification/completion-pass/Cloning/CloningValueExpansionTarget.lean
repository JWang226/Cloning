import Cloning.CloningValueExpansionThreshold

/-! Concrete small-error gains straddle the actual scalar fidelity target.
These brackets do not assume an inverse branch or a target-attainment premise. -/
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem scaled_infidelity_tendsto {f : ℝ→ℝ} {a c : ℝ} (ha : 0<a) (hc : 0<c)
    (hlim : Tendsto (fun x=>(1-f x)/x^2) (𝓝[>] (0:ℝ)) (𝓝 a)) :
    Tendsto (fun ε=>(1-f (c*Real.sqrt (ε/a)))/ε) (𝓝[>] (0:ℝ)) (𝓝 (c^2)) := by
  let delta : ℝ→ℝ := fun ε=>c*Real.sqrt (ε/a)
  have hd : Tendsto delta (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      simpa only [delta,zero_div,Real.sqrt_zero,mul_zero] using
        ((hid.div_const a).sqrt.const_mul c)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hc (Real.sqrt_pos.mpr (div_pos hε ha))
  have ht := (hlim.comp hd).mul_const (c^2/a)
  rw [mul_div_cancel₀ _ ha.ne'] at ht
  apply ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0<ε := hε
  dsimp only [Function.comp_apply,delta]
  rw [mul_pow,Real.sq_sqrt (div_pos hε0 ha).le]
  field_simp [ha.ne',hc.ne',hε0.ne']
  <;> ring

/-- Gains just below and above the predicted leading scale give actual
squared fidelities respectively above and below `1-ε`. -/
theorem fidelity_target_brackets {f : ℝ→ℝ} {a eta : ℝ}
    (ha : 0<a) (heta : 0<eta) (heta1 : eta<1)
    (hlim : Tendsto (fun x=>(1-f x)/x^2) (𝓝[>] (0:ℝ)) (𝓝 a)) :
    ∀ᶠε in 𝓝[>] (0:ℝ),
      1-ε<f ((1-eta)*Real.sqrt (ε/a)) ∧
      f ((1+eta)*Real.sqrt (ε/a))<1-ε := by
  have hl := scaled_infidelity_tendsto ha (sub_pos.mpr heta1) hlim
  have hu := scaled_infidelity_tendsto ha (show 0<1+eta by linarith) hlim
  have hcl : (1-eta)^2<1 := by nlinarith
  have hcu : 1<(1+eta)^2 := by nlinarith
  filter_upwards [self_mem_nhdsWithin,hl.eventually_lt_const hcl,
    hu.eventually_const_lt hcu] with ε hε hL hU
  have hε0 : 0<ε := hε
  constructor
  · have h := (div_lt_one hε0).mp hL
    linarith
  · have h := (one_lt_div hε0).mp hU
    linarith

theorem universal_target_brackets {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d)
    {eta : ℝ} (heta : 0<eta) (heta1 : eta<1) :
    ∀ᶠε in 𝓝[>] (0:ℝ),
      1-ε<universalValue (1+(1-eta)*Real.sqrt (ε/universalCoefficient p)) p^2 ∧
      universalValue (1+(1+eta)*Real.sqrt (ε/universalCoefficient p)) p^2<1-ε :=
  fidelity_target_brackets (universalCoefficient_pos hd p) heta heta1
    (universal_infidelity_div_sq_tendsto p)

theorem pct_target_brackets {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d)
    {eta : ℝ} (heta : 0<eta) (heta1 : eta<1) :
    ∀ᶠε in 𝓝[>] (0:ℝ),
      1-ε<pctValue (1+(1-eta)*Real.sqrt (ε/pctCoefficient p)) p^2 ∧
      pctValue (1+(1+eta)*Real.sqrt (ε/pctCoefficient p)) p^2<1-ε :=
  fidelity_target_brackets (pctCoefficient_pos hd p) heta heta1
    (pct_infidelity_div_sq_tendsto p)

theorem knownCoefficient_pos {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d) :
    0<knownCoefficient p := by
  let ij : PairIndex d := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0:ℕ)<1; omega⟩
  apply Finset.sum_pos
  · intro a _
    exact div_pos (by norm_num) (mul_pos (by norm_num) (p.ratio_pos a))
  · exact ⟨ij,Finset.mem_univ ij⟩

theorem known_target_brackets {d : ℕ} (hd : 2≤d) (p : SimpleSpectrum d)
    {eta : ℝ} (heta : 0<eta) (heta1 : eta<1) :
    ∀ᶠε in 𝓝[>] (0:ℝ),
      1-ε<orbitalValue (1+(1-eta)*Real.sqrt (ε/knownCoefficient p)) p^2 ∧
      orbitalValue (1+(1+eta)*Real.sqrt (ε/knownCoefficient p)) p^2<1-ε :=
  fidelity_target_brackets (knownCoefficient_pos hd p) heta heta1
    (known_infidelity_div_sq_tendsto p)

end Cloning.ValueExpansion
