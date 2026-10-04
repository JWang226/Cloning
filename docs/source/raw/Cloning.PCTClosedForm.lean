import Cloning.Main

/-! The explicit radical form of the PCT fidelity in the manuscript. -/
noncomputable section
open scoped BigOperators
namespace Cloning.Thermal

theorem fidelity_pct_unrationalized {g q : ℝ} (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    fidelity q (pct g q) =
      (1-q)/(Real.sqrt (g+(g-1)*q)-Real.sqrt (q*(g-1+g*q))) := by
  have hg0 : 0 < g := by linarith
  have hg1 : 0 ≤ g-1 := by linarith
  have hdpos : 0 < g+(g-1)*q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)
  have hd : g+(g-1)*q ≠ 0 := hdpos.ne'
  have hs : Real.sqrt (g+(g-1)*q) ≠ 0 := (Real.sqrt_pos.2 hdpos).ne'
  have hn : Real.sqrt ((1-q)*(1-pct g q)) = (1-q)/Real.sqrt (g+(g-1)*q) := by
    have he : (1-q)*(1-pct g q)=(1-q)^2/(g+(g-1)*q) := by
      unfold pct
      field_simp [hd]
      <;> ring
    rw [he,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (sub_nonneg.mpr hq1.le)]
  have hr : Real.sqrt (q*pct g q)=Real.sqrt (q*(g-1+g*q))/Real.sqrt (g+(g-1)*q) := by
    unfold pct
    rw [← mul_div_assoc,Real.sqrt_div (mul_nonneg hq0 (by positivity))]
  unfold fidelity
  rw [hn,hr]
  have he : 1-Real.sqrt (q*(g-1+g*q))/Real.sqrt (g+(g-1)*q)=
      (Real.sqrt (g+(g-1)*q)-Real.sqrt (q*(g-1+g*q)))/Real.sqrt (g+(g-1)*q) := by
    field_simp [hs]
  rw [he,div_div_div_cancel_right₀ hs]

theorem fidelity_pct_closedForm {g q : ℝ} (hg : 1 < g)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    fidelity q (pct g q)=
      (Real.sqrt (g+(g-1)*q)+Real.sqrt (q*(g-1+g*q)))/(g*(1+q)) := by
  have hg0 : 0 < g := by linarith
  have hg1 : 0 ≤ g-1 := by linarith
  have hrad : 0 ≤ q*(g-1+g*q) := mul_nonneg hq0 (add_nonneg hg1 (mul_nonneg hg0.le hq0))
  have hdpos : 0 < g+(g-1)*q := add_pos_of_pos_of_nonneg hg0 (mul_nonneg hg1 hq0)
  have hsum : 0 < g*(1+q) := by positivity
  have hradlt : q*(g-1+g*q) < g+(g-1)*q := by
    have hp := mul_pos (sub_pos.mpr hq1) hsum
    nlinarith
  have hd : 0 < Real.sqrt (g+(g-1)*q)-Real.sqrt (q*(g-1+g*q)) :=
    sub_pos.mpr (Real.sqrt_lt_sqrt hrad hradlt)
  rw [fidelity_pct_unrationalized hg hq0 hq1]
  apply (div_eq_div_iff hd.ne' hsum.ne').mpr
  nlinarith [Real.sq_sqrt hdpos.le,Real.sq_sqrt hrad]

end Cloning.Thermal
namespace Cloning

theorem pctValue_closedForm {d : ℕ} {g : ℝ} (hg : 1<g) (p : SimpleSpectrum d) :
    pctValue g p=(Real.sqrt (2*g-1)/g)^(((d : ℝ)-1)/2)*
      ∏ ij : PairIndex d,
        (Real.sqrt (g+(g-1)*p.ratio ij)+Real.sqrt (p.ratio ij*(g-1+g*p.ratio ij)))/
          (g*(1+p.ratio ij)) := by
  have hc : Thermal.classicalBase (2*g-1)=Real.sqrt (2*g-1)/g := by
    unfold Thermal.classicalBase
    field_simp
    <;> ring
  simp only [pctValue,classicalValue,hc]
  congr 1
  apply Finset.prod_congr rfl
  intro ij _
  exact Thermal.fidelity_pct_closedForm hg (p.ratio_pos ij).le (p.ratio_lt_one ij)

end Cloning
