import Cloning.SpectralRatioMajorization

/-! An exact three-dimensional counterexample to monotonicity under
majorization alone. All numerical comparisons use rational square bounds. -/
noncomputable section
open scoped BigOperators
namespace Cloning.ValueComparison
set_option maxHeartbeats 1200000

def concentratedSpectrum : SimpleSpectrum 3 where
  eigenvalue := ![(9:ℝ)/10,3/50,1/25]
  positive := by intro i; fin_cases i <;> norm_num
  strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  normalized := by norm_num [Fin.sum_univ_succ]

def majorizedSpectrum : SimpleSpectrum 3 where
  eigenvalue := ![(4:ℝ)/5,4/25,1/25]
  positive := by intro i; fin_cases i <;> norm_num
  strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  normalized := by norm_num [Fin.sum_univ_succ]

theorem counterexample_majorization : SpectrumMajorizedBy majorizedSpectrum concentratedSpectrum := by
  intro m
  by_cases hm : m≤3
  · interval_cases m <;>
      norm_num [majorizedSpectrum,concentratedSpectrum,Finset.sum_filter,Fin.sum_univ_succ]
  · have h0 : 0<m := by omega
    have h1 : 1<m := by omega
    have h2 : 2<m := by omega
    norm_num [majorizedSpectrum,concentratedSpectrum,Finset.sum_filter,Fin.sum_univ_succ,h0,h1,h2]

private theorem orbitalValue_three (g : ℝ) (p : SimpleSpectrum 3) :
    orbitalValue g p =
      Thermal.modeFactor g (p.eigenvalue 1/p.eigenvalue 0)*
      Thermal.modeFactor g (p.eigenvalue 2/p.eigenvalue 0)*
      Thermal.modeFactor g (p.eigenvalue 2/p.eigenvalue 1) := by
  classical
  let a : PairIndex 3 := ⟨(0,1),by decide⟩
  let b : PairIndex 3 := ⟨(0,2),by decide⟩
  let c : PairIndex 3 := ⟨(1,2),by decide⟩
  have hu : (Finset.univ : Finset (PairIndex 3))={a,b,c} := by decide
  rw [orbitalValue,hu]
  simp [a,b,c,SimpleSpectrum.ratio,mul_assoc]

private theorem mode_ten_upper (q s u : ℝ) (hq : 0≤q) (hs : 0≤s)
    (hrad : q*(9+q)≤s^2) (hu : (3163/1000+s)/(10+q)≤u) :
    Thermal.modeFactor 10 q≤u := by
  have h10 : Real.sqrt (10:ℝ)≤3163/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hsqrt : Real.sqrt (q*(10-1+q))≤s := Real.sqrt_le_iff.mpr ⟨hs,by norm_num; exact hrad⟩
  unfold Thermal.modeFactor
  exact (div_le_div_of_nonneg_right (add_le_add h10 hsqrt) (by linarith)).trans hu

private theorem mode_ten_lower (q s l : ℝ) (hq : 0≤q)
    (hrad : s^2≤q*(9+q)) (hl : l≤(3162/1000+s)/(10+q)) :
    l≤Thermal.modeFactor 10 q := by
  have h10 : (3162:ℝ)/1000≤Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
  have hsqrt : s≤Real.sqrt (q*(10-1+q)) := Real.le_sqrt_of_sq_le (by norm_num; exact hrad)
  unfold Thermal.modeFactor
  exact hl.trans (div_le_div_of_nonneg_right (add_le_add h10 hsqrt) (by linarith))

/-- The more majorized spectrum has fidelity strictly below the exact
rational separator 0.078. -/
theorem majorizedSpectrum_orbital_lt : orbitalValue 10 majorizedSpectrum <39/500 := by
  rw [orbitalValue_three]
  norm_num [majorizedSpectrum,Matrix.cons_val_two] 
  have h1 : Thermal.modeFactor 10 (1/5)≤444/1000 :=
    mode_ten_upper _ (1357/1000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : Thermal.modeFactor 10 (1/20)≤382/1000 :=
    mode_ten_upper _ (673/1000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : Thermal.modeFactor 10 (1/4)≤457/1000 :=
    mode_ten_upper _ (1521/1000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hn1 := (Thermal.modeFactor_pos (by norm_num : (1:ℝ)<10)
    (by norm_num : (0:ℝ)≤1/5) (by norm_num : (1:ℝ)/5<1)).le
  have hn2 := (Thermal.modeFactor_pos (by norm_num : (1:ℝ)<10)
    (by norm_num : (0:ℝ)≤1/20) (by norm_num : (1:ℝ)/20<1)).le
  have hn3 := (Thermal.modeFactor_pos (by norm_num : (1:ℝ)<10)
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1:ℝ)/4<1)).le
  exact lt_of_le_of_lt (mul_le_mul (mul_le_mul h1 h2 hn2 (by norm_num)) h3 hn3
    (by norm_num)) (by norm_num)

/-- The less majorized spectrum has fidelity strictly above 0.078. -/
theorem concentratedSpectrum_orbital_gt : (39:ℝ)/500<orbitalValue 10 concentratedSpectrum := by
  rw [orbitalValue_three]
  norm_num [concentratedSpectrum,Matrix.cons_val_two]
  have h1 : (391:ℝ)/1000≤Thermal.modeFactor 10 (1/15) :=
    mode_ten_lower _ (777/1000) _ (by norm_num) (by norm_num) (by norm_num)
  have h2 : (377:ℝ)/1000≤Thermal.modeFactor 10 (2/45) :=
    mode_ten_lower _ (634/1000) _ (by norm_num) (by norm_num) (by norm_num)
  have h3 : (534:ℝ)/1000≤Thermal.modeFactor 10 (2/3) :=
    mode_ten_lower _ (2538/1000) _ (by norm_num) (by norm_num) (by norm_num)
  have hn1 : 0≤Thermal.modeFactor 10 (1/15) := le_trans (by norm_num) h1
  have hn2 : 0≤Thermal.modeFactor 10 (2/45) := le_trans (by norm_num) h2
  exact lt_of_lt_of_le (by norm_num : (39:ℝ)/500<(391/1000)*(377/1000)*(534/1000))
    (mul_le_mul (mul_le_mul h1 h2 (by norm_num) hn1) h3 (by norm_num)
      (mul_nonneg hn1 hn2))

/-- Majorization alone does not imply larger orbital cloning fidelity. -/
theorem majorization_does_not_order_orbital :
    SpectrumMajorizedBy majorizedSpectrum concentratedSpectrum ∧
      orbitalValue 10 majorizedSpectrum<orbitalValue 10 concentratedSpectrum :=
  ⟨counterexample_majorization,majorizedSpectrum_orbital_lt.trans concentratedSpectrum_orbital_gt⟩

/-- The same explicit spectra also disprove monotonicity of the universal
value under majorization: its positive classical factor is spectrum-independent. -/
theorem majorization_does_not_order_universal :
    SpectrumMajorizedBy majorizedSpectrum concentratedSpectrum ∧
      universalValue 10 majorizedSpectrum<universalValue 10 concentratedSpectrum := by
  refine ⟨counterexample_majorization, ?_⟩
  exact mul_lt_mul_of_pos_left majorization_does_not_order_orbital.2
    (classicalValue_pos (by norm_num : (0:ℝ)<10) 3)

end Cloning.ValueComparison
