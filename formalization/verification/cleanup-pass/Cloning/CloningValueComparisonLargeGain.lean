import Cloning.CloningValueComparisonInfimum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Quantitative large-gain behavior of the two all-state minimax bounds. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.ValueComparison
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

def allStateLowerBound (d : ℕ) (g : ℝ) : ℝ := g^(-((d:ℝ)^2-1)/2)
def allStateUpperBound (d : ℕ) (g : ℝ) : ℝ :=
  classicalValue g d*g^(-((d:ℝ)*((d:ℝ)-1))/4)

theorem allStateUpperBound_factor (d : ℕ) {g : ℝ} (hg : 0<g) :
    allStateUpperBound d g = (2*g/(1+g))^(((d:ℝ)-1)/2)*g^(-((d:ℝ)^2-1)/4) := by
  have hs : Real.sqrt g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  have hbase : Thermal.classicalBase g=(2*g/(1+g))*g^(-(1/2:ℝ)) := by
    rw [Real.rpow_neg hg.le,←Real.sqrt_eq_rpow]
    dsimp only [Thermal.classicalBase]
    field_simp [hs,show 1+g≠0 by linarith]
    nlinarith [Real.sq_sqrt hg.le]
  dsimp only [allStateUpperBound,classicalValue]
  rw [hbase,Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hg.le,
    mul_assoc,←Real.rpow_add hg]
  congr 1
  congr 1
  ring

theorem allStateUpperBound_largeGain_bounds (d : ℕ) (hd : 1≤d) {g : ℝ} (hg : 1≤g) :
    g^(-((d:ℝ)^2-1)/4) ≤ allStateUpperBound d g ∧
      allStateUpperBound d g ≤ 2^(((d:ℝ)-1)/2)*g^(-((d:ℝ)^2-1)/4) := by
  have hg0 : 0<g := by linarith
  have ha : 0≤((d:ℝ)-1)/2 := by
    have : (1:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hc1 : 1≤2*g/(1+g) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hc2 : 2*g/(1+g)≤2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  rw [allStateUpperBound_factor d hg0]
  constructor
  · simpa only [one_mul,Real.one_rpow] using
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) hc1 ha)
        (Real.rpow_nonneg hg0.le _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) hc2 ha) (Real.rpow_nonneg hg0.le _)

/-- The upper bound has an exact positive leading constant at large gain. -/
theorem allStateUpperBound_largeGain_tendsto (d : ℕ) :
    Tendsto (fun g => allStateUpperBound d g/g^(-((d:ℝ)^2-1)/4)) atTop
      (𝓝 (2^(((d:ℝ)-1)/2))) := by
  have ht : Tendsto (fun g : ℝ => 2/(1+g⁻¹)) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.div
      (tendsto_const_nhds.add tendsto_inv_atTop_zero) (by norm_num : (1+(0:ℝ))≠0))
  have hp := ht.rpow_const (p:=((d:ℝ)-1)/2) (Or.inl (by norm_num : (2:ℝ)≠0))
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with g hg
  rw [allStateUpperBound_factor d hg,mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hg _).ne']
  congr 1
  field_simp [hg.ne']
  <;> ring

/-- The lower bound is exactly a power with twice the upper bound's exponent. -/
theorem allStateLowerBound_largeGain_ratio (d : ℕ) {g : ℝ} (hg : 0<g) :
    allStateLowerBound d g/g^(-((d:ℝ)^2-1)/2)=1 :=
  div_self (Real.rpow_pos_of_pos hg _).ne'

end Cloning.ValueComparison
