import Cloning.PCTRankAdaptedWerner
import Cloning.WernerAsymptotics
import Cloning.Main

/-! The exact support factor has the manuscript's Grassmannian limit;
the internal covariance-inflation factor is strictly below one. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.PCTRankAdapted
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem wernerScale_eq_vacuum (n m s : ℕ) (hnm : n ≤ m) :
    wernerScale n m s = Cloning.WernerAsymptotics.coefficient n m s 0 := by
  have h := Cloning.Occupation.werner_dimension_identity n m s m hnm
  have hc : (Nat.choose m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hnm).ne'
  simpa only [wernerScale, Cloning.WernerAsymptotics.coefficient, Nat.sub_zero,
    div_self hc, mul_one] using h

theorem wernerScale_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (s : ℕ) :
    Tendsto (fun n => wernerScale n (m n) s) atTop (𝓝 ((1/γ)^s)) := by
  have ht := Cloning.WernerAsymptotics.coefficient_tendsto m hγ h s 0
  simp only [pow_zero, mul_one] at ht
  apply ht.congr'
  filter_upwards [Cloning.WernerAsymptotics.eventually_add_le m hγ h 0] with n hn
  exact (wernerScale_eq_vacuum n (m n) s (by simpa using hn)).symm

theorem supportFactor_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (small large : ℕ) :
    Tendsto (fun n => supportFactor n (m n) small large) atTop
      (𝓝 ((1/γ)^large / (1/γ)^small)) :=
  (wernerScale_tendsto m hγ h large).div (wernerScale_tendsto m hγ h small)
    (pow_ne_zero _ (one_div_ne_zero (by linarith)))

theorem sqrt_supportFactor_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) (small large : ℕ) :
    Tendsto (fun n => Real.sqrt (supportFactor n (m n) small large)) atTop
      (𝓝 (γ ^ (-((large : ℝ)-(small : ℝ))/2))) := by
  have hg : 0 < γ := by linarith
  have ht := (supportFactor_tendsto m hγ h small large).sqrt
  have he : Real.sqrt ((1/γ)^large / (1/γ)^small) =
      γ ^ (-((large : ℝ)-(small : ℝ))/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_sub (one_div_pos.mpr hg), ← Real.rpow_mul (one_div_pos.mpr hg).le]
    rw [one_div, Real.inv_rpow hg.le, ← Real.rpow_neg hg.le]
    congr 1
    ring
  exact he ▸ ht

/-- Covariance inflation in the internal maximally mixed state contributes
exactly the extra factor shown in the projector PCT bound. -/
theorem classicalValue_inflated (γ : ℝ) (r : ℕ) :
    Cloning.classicalValue (2*γ-1) r =
      (Real.sqrt (2*γ-1)/γ) ^ (((r : ℝ)-1)/2) := by
  unfold Cloning.classicalValue Cloning.Thermal.classicalBase
  congr 1
  by_cases hg : γ = 0
  · simp [hg]
  · field_simp
    <;> ring

theorem classicalValue_inflated_lt_one {γ : ℝ} (hγ : 1 < γ) {r : ℕ} (hr : 1 < r) :
    Cloning.classicalValue (2*γ-1) r < 1 := by
  unfold Cloning.classicalValue
  have hg : 1 < 2*γ-1 := by linarith
  apply Real.rpow_lt_one (Cloning.Thermal.classicalBase_pos (by linarith)).le
    (Cloning.Thermal.classicalBase_lt_one hg)
  have hr' : (1 : ℝ) < r := by exact_mod_cast hr
  linarith

end Cloning.PCTRankAdapted
