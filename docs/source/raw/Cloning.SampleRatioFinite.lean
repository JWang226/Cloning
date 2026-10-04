import Cloning.SampleRatioThreshold
import Cloning.PCTRankAdaptedFactor

/-! Exact finite binomial-ratio certification for the sample threshold. -/
noncomputable section
open scoped BigOperators
namespace Cloning.SampleRatio
open Cloning.PCTRankAdapted Cloning.WernerAsymptotics
set_option backward.isDefEq.respectTransparency false

theorem wernerScale_product (n m a : ℕ) (hnm : n≤m) :
    wernerScale n m a = ∏ j ∈ Finset.range a,
      ((n:ℝ)+j+1)/((m:ℝ)+j+1) := by
  simp_rw [wernerScale_eq_vacuum n m a hnm]
  induction a with
  | zero => simp [coefficient_zero_zero n m hnm]
  | succ a ih =>
    rw [coefficient_succ_modes n m a 0 hnm,Finset.prod_range_succ,ih]
    ring

theorem wernerScale_power_lower (N M a : ℕ) (hN : 0<N) :
    ((N:ℝ)/(N+M))^a ≤ wernerScale N (N+M) a := by
  rw [wernerScale_product N (N+M) a (Nat.le_add_right N M)]
  simpa only [Nat.cast_add] using finite_product_lower a N M hN

/-- The finite binomial ratio already exceeds the requested squared fidelity
under the stated sample-ratio condition. No limiting approximation is used. -/
theorem wernerScale_ge_target (N M a : ℕ) (hN : 0<N) (hM : 0<M) (ha : 0<a)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (hR : threshold a ε ≤ (N:ℝ)/M) :
    1-ε ≤ wernerScale N (N+M) a := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hh := (power_fidelity_iff (by exact_mod_cast ha) hε hε1 (div_pos hn hm)).mpr hR
  have he : (1+((N:ℝ)/M)⁻¹)^(-(a:ℝ)) = ((N:ℝ)/(N+M))^a := by
    have hb : 1+((N:ℝ)/M)⁻¹=((N:ℝ)+M)/N := by field_simp
    rw [hb,Real.rpow_neg (by positivity),Real.rpow_natCast,div_pow,inv_div,div_pow]
  rw [he] at hh
  exact hh.trans (wernerScale_power_lower N M a hN)

end Cloning.SampleRatio
