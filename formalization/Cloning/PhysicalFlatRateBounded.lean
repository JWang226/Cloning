import Cloning.PhysicalFlatRateRounded

/-! The all-channel upper rate for every bounded rounding of γn. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.PhysicalFlatConverse
set_option maxHeartbeats 1200000

theorem ratio_error_of_sample_error (m n : ℕ) (γ B : ℝ) (hn : 1≤n)
    (h : |(m:ℝ)-γ*n|≤B) : |(m:ℝ)/(n:ℝ)-γ|≤B/(n:ℝ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (m:ℝ)/(n:ℝ)-γ=((m:ℝ)-γ*n)/(n:ℝ) := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos hn0]
  exact div_le_div_of_nonneg_right h hn0.le

theorem ratio_tendsto_of_bounded_rounding (m : ℕ→ℕ) (γ : ℝ)
    (hround : ∃B : ℝ,∀ᶠ (n : ℕ) in atTop,|(m n:ℝ)-γ*n|≤B) :
    Tendsto (fun n : ℕ=>(m n:ℝ)/(n:ℝ)) atTop (𝓝 γ) := by
  obtain ⟨B,hB⟩ := hround
  have hi : Tendsto (fun n : ℕ=>B/(n:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul B
    simpa only [mul_zero,← div_eq_mul_inv] using h
  have hz : Tendsto (fun n : ℕ=>|(m n:ℝ)/(n:ℝ)-γ|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _=>abs_nonneg _))
      (by filter_upwards [hB,eventually_ge_atTop 1] with n hb hn
          exact ratio_error_of_sample_error (m n) n γ B hn hb) hi
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)

/-- Arbitrary bounded rounding, with no convergence or rate assumption on
any quantum output or moment. -/
theorem eventually_minimaxValue_bounded_rounding_rate (r k : ℕ) (hr : 0<r)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hround : ∃B : ℝ,∀ᶠ (n : ℕ) in atTop,|(m n:ℝ)-γ*n|≤B) :
    ∃C : ℝ,0≤C ∧ ∀ᶠ (n : ℕ) in atTop,
      minimaxValue r k hr n (m n)≤γ^(-(((r*k:ℕ):ℝ)/2))+C/(n:ℝ) := by
  obtain ⟨B0,hB0⟩ := hround
  let B := max B0 0
  have hB : 0≤B := le_max_right _ _
  have hb : ∀ᶠ (n : ℕ) in atTop,|(m n:ℝ)-γ*n|≤B :=
    hB0.mono (fun _ h=>h.trans (le_max_left _ _))
  let p : ℝ := -(((r*k:ℕ):ℝ)/2)
  let x : ℕ→ℝ := fun n=>(m n:ℝ)/(n:ℝ)
  let D := flatConverseRateConstant r k
  have hD : 0≤D := flatConverseRateConstant_nonneg r k
  have hg : 0<γ := zero_lt_one.trans hγ
  have hx : Tendsto x atTop (𝓝 γ) := ratio_tendsto_of_bounded_rounding m γ ⟨B,hb⟩
  have hd := Real.hasDerivAt_rpow_const (p := p) (Or.inl hg.ne')
  obtain ⟨L,hL,hLbound⟩ := (hd.isBigO_sub.comp_tendsto hx).exists_pos
  have he : ∀ᶠ (n : ℕ) in atTop,|x n^p-γ^p|≤(L*B)/(n:ℝ) := by
    filter_upwards [hLbound.bound,hb,eventually_ge_atTop 1] with n hbound hb hn
    have hh : |x n^p-γ^p|≤L*|x n-γ| := by
      simpa only [Function.comp_apply,Real.norm_eq_abs] using hbound
    exact hh.trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
        (ratio_error_of_sample_error (m n) n γ B hn hb) hL.le)
  have hpow := hd.continuousAt.tendsto.comp hx
  have hub : ∀ᶠ (n : ℕ) in atTop,x n^p≤γ^p+1 :=
    hpow.eventually (eventually_le_nhds (by linarith))
  have hmn : ∀ᶠ (n : ℕ) in atTop,n≤m n := by
    filter_upwards [hx.eventually (eventually_ge_nhds hγ),eventually_ge_atTop 1] with n hn hn1
    have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have h := (le_div_iff₀ hnR).mp hn
    have hR : (n:ℝ)≤m n := by simpa only [one_mul] using h
    exact_mod_cast hR
  refine ⟨L*B+(γ^p+1)*D,by positivity,?_⟩
  filter_upwards [he,hub,hmn,eventually_minimaxValue_rate r k hr,eventually_ge_atTop 1]
    with n he hub hmn hbound hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hf : x n^p≤γ^p+(L*B)/(n:ℝ) := by
    have hh := le_abs_self (x n^p-γ^p)
    linarith
  have hm := hbound (m n) hmn
  change minimaxValue r k hr n (m n)≤x n^p*(1+D/(n:ℝ)) at hm
  apply hm.trans
  have hm2 := mul_le_mul_of_nonneg_right hub (div_nonneg hD hnR.le)
  change x n^p*(1+D/(n:ℝ))≤γ^p+(L*B+(γ^p+1)*D)/(n:ℝ)
  calc
    _ = x n^p+x n^p*(D/(n:ℝ)) := by ring
    _ ≤ (γ^p+(L*B)/(n:ℝ))+(γ^p+1)*(D/(n:ℝ)) := add_le_add hf hm2
    _ = _ := by ring

/-- The manuscript convention m_n=γn+O(1) suffices. -/
theorem eventually_minimaxValue_of_sample_remainder_isBigO (r k : ℕ) (hr : 0<r)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hround : (fun n : ℕ=>(m n:ℝ)-γ*n)=O[atTop] (fun _ : ℕ=>(1:ℝ))) :
    ∃C : ℝ,0≤C ∧ ∀ᶠ (n : ℕ) in atTop,
      minimaxValue r k hr n (m n)≤γ^(-(((r*k:ℕ):ℝ)/2))+C/(n:ℝ) := by
  obtain ⟨B,hB,hbound⟩ := hround.exists_pos
  apply eventually_minimaxValue_bounded_rounding_rate r k hr m γ hγ
  exact ⟨B,by simpa only [Real.norm_eq_abs,abs_one,mul_one] using hbound.bound⟩

/-- Only the upper excess is asserted here; a matching lower rate is a
separate quantitative achievability question. -/
theorem minimaxValue_upper_excess_isBigO (r k : ℕ) (hr : 0<r)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hround : (fun n : ℕ=>(m n:ℝ)-γ*n)=O[atTop] (fun _ : ℕ=>(1:ℝ))) :
    (fun n : ℕ=>max (minimaxValue r k hr n (m n)-γ^(-(((r*k:ℕ):ℝ)/2))) 0)
      =O[atTop] (fun n : ℕ=>1/(n:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := eventually_minimaxValue_of_sample_remainder_isBigO r k hr m γ hγ hround
  apply IsBigO.of_bound C
  filter_upwards [hbound] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤1/(n:ℝ)),mul_one_div]
  exact max_le (by linarith) (div_nonneg hC (Nat.cast_nonneg n))

end Cloning.PhysicalFlatConverse
