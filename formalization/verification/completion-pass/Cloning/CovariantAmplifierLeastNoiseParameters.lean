import Cloning.CovariantAmplifierComposite

/-! Exact parameter conversions from the composite gains to the literal
negative-binomial idler channel. -/
noncomputable section
namespace Cloning.CovariantAmplifier
open Cloning.Thermal

lemma amplified_pos {γ q : ℝ} (hγ : 1<γ) (hq0 : 0≤q) (hq1 : q<1) :
    0<amplified γ q := lt_of_le_of_lt hq0 (lt_amplified hγ hq1)

lemma amplified_complement_inv {γ q : ℝ} (hγ : 1<γ) (hq1 : q<1) :
    (1-amplified γ q)⁻¹=modeGain γ q := by
  unfold amplified modeGain
  rw [sub_sub_cancel, inv_div]

lemma amplified_odds {γ q : ℝ} (hγ : 1<γ) (hq1 : q<1) :
    amplified γ q/(1-amplified γ q)=modeGain γ q-1 := by
  have hg : γ≠0 := ne_of_gt (lt_trans zero_lt_one hγ)
  have hq : 1-q≠0 := ne_of_gt (sub_pos.mpr hq1)
  unfold amplified modeGain
  rw [sub_sub_cancel]
  field_simp
  <;> ring

lemma amplified_sqrt_odds {γ q : ℝ} (hγ : 1<γ) (hq0 : 0≤q) (hq1 : q<1) :
    Real.sqrt (amplified γ q)/Real.sqrt (1-amplified γ q)=
      Real.sqrt (modeGain γ q-1) := by
  rw [← Real.sqrt_div (amplified_nonneg hγ hq0 hq1), amplified_odds hγ hq1]

lemma amplified_gaussian_exponent {γ q x : ℝ} (hγ : 1<γ) (hq1 : q<1) :
    -x/(2*(1-amplified γ q))=-(modeGain γ q*x)/2 := by
  rw [div_mul_eq_div_div, div_eq_mul_inv, amplified_complement_inv hγ hq1]
  ring

end Cloning.CovariantAmplifier
