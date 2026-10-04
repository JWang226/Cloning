import Cloning.PhysicalFlatRate
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The fixed-ratio finite upper rate for the concrete rounded sample sizes. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.PhysicalFlatConverse
set_option maxHeartbeats 1000000

def floorOutput (γ : ℝ) (n : ℕ) : ℕ := ⌊γ*(n:ℝ)⌋₊

theorem floorOutput_ratio_error (γ : ℝ) (hγ : 0≤γ) (n : ℕ) (hn : 1≤n) :
    |(floorOutput γ n:ℝ)/(n:ℝ)-γ|≤1/(n:ℝ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (floorOutput γ n:ℝ)/(n:ℝ)-γ=
      ((floorOutput γ n:ℝ)-γ*n)/(n:ℝ) := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos hn0]
  exact div_le_div_of_nonneg_right (Nat.abs_floor_sub_le (mul_nonneg hγ (Nat.cast_nonneg n))) hn0.le

theorem floorOutput_ratio_tendsto (γ : ℝ) (hγ : 0≤γ) :
    Tendsto (fun n : ℕ=>(floorOutput γ n:ℝ)/(n:ℝ)) atTop (𝓝 γ) := by
  have hi : Tendsto (fun n : ℕ=>1/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ=>|(floorOutput γ n:ℝ)/(n:ℝ)-γ|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _=>abs_nonneg _))
      (by filter_upwards [eventually_ge_atTop 1] with n hn; exact floorOutput_ratio_error γ hγ n hn) hi
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)

theorem le_floorOutput (γ : ℝ) (hγ : 1≤γ) (n : ℕ) : n≤floorOutput γ n := by
  apply Nat.le_floor
  nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]

/-- For m_n=floor(γn), the all-channel optimum is at most the limiting value
plus C/n, with C depending only on r,k,γ. -/
theorem eventually_minimaxValue_floor_rate (r k : ℕ) (hr : 0<r)
    (γ : ℝ) (hγ : 1<γ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (n : ℕ) in atTop,
      minimaxValue r k hr n (floorOutput γ n)≤γ^(-(((r*k:ℕ):ℝ)/2))+C/(n:ℝ) := by
  let p : ℝ := -(((r*k:ℕ):ℝ)/2)
  let x : ℕ→ℝ := fun n=>(floorOutput γ n:ℝ)/(n:ℝ)
  let D := flatConverseRateConstant r k
  have hD : 0≤D := flatConverseRateConstant_nonneg r k
  have hg : 0<γ := zero_lt_one.trans hγ
  have hx : Tendsto x atTop (𝓝 γ) := floorOutput_ratio_tendsto γ hg.le
  have hd := Real.hasDerivAt_rpow_const (p := p) (Or.inl hg.ne')
  have ho := hd.isBigO_sub.comp_tendsto hx
  obtain ⟨L,hL,hLbound⟩ := ho.exists_pos
  have he : ∀ᶠ (n : ℕ) in atTop,|x n^p-γ^p|≤L/(n:ℝ) := by
    filter_upwards [hLbound.bound,eventually_ge_atTop 1] with n hbound hn
    have hb : |x n^p-γ^p|≤L*|x n-γ| := by
      simpa only [Function.comp_apply,Real.norm_eq_abs] using hbound
    exact hb.trans (by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (floorOutput_ratio_error γ hg.le n hn) hL.le)
  have hpow := hd.continuousAt.tendsto.comp hx
  have hub : ∀ᶠ (n : ℕ) in atTop,x n^p≤γ^p+1 :=
    hpow.eventually (eventually_le_nhds (by linarith))
  refine ⟨L+(γ^p+1)*D,by positivity,?_⟩
  filter_upwards [he,hub,eventually_minimaxValue_rate r k hr,eventually_ge_atTop 1]
    with n he hub hbound hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hf : x n^p≤γ^p+L/(n:ℝ) := by
    have hh := le_abs_self (x n^p-γ^p)
    linarith
  have hm := hbound (floorOutput γ n) (le_floorOutput γ hγ.le n)
  change minimaxValue r k hr n (floorOutput γ n)≤x n^p*(1+D/(n:ℝ)) at hm
  apply hm.trans
  have hm2 := mul_le_mul_of_nonneg_right hub (div_nonneg hD hn0.le)
  change x n^p*(1+D/(n:ℝ))≤γ^p+(L+(γ^p+1)*D)/(n:ℝ)
  calc
    _ = x n^p+x n^p*(D/(n:ℝ)) := by ring
    _ ≤ (γ^p+L/(n:ℝ))+(γ^p+1)*(D/(n:ℝ)) := add_le_add hf hm2
    _ = _ := by ring

end Cloning.PhysicalFlatConverse
