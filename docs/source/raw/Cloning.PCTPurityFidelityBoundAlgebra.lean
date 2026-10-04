import Cloning.PCTGaussianCovariance
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Module

/-! Uniform rational-curve norm estimates used for physical projector PCT
purity domination. The norm on matrices is explicitly Frobenius. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder NNReal Matrix.Norms.Frobenius
namespace Cloning.PCTPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000

lemma rational_curve_difference {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B A C : E) (t a : ℝ) (hd : 1+t^2*a^2≠0) :
    (1+t^2*a^2)⁻¹ • (B+t • A+t^2 • C)-B=
      (1+t^2*a^2)⁻¹ • (t • A+t^2 • (C-a^2 • B)) := by
  have hc : (1+t^2*a^2)⁻¹-1= -((1+t^2*a^2)⁻¹*t^2*a^2) := by
    field_simp [hd]
    ring
  have hB : (1+t^2*a^2)⁻¹ • B-B= -((1+t^2*a^2)⁻¹*t^2*a^2) • B := by
    calc
      _ = ((1+t^2*a^2)⁻¹-1) • B := by rw [sub_smul,one_smul]
      _ = _ := by rw [hc]
  calc
    _ = ((1+t^2*a^2)⁻¹ • B-B)+
        ((1+t^2*a^2)⁻¹*t) • A+((1+t^2*a^2)⁻¹*t^2) • C := by module
    _ = _ := by rw [hB]; module

set_option backward.isDefEq.respectTransparency false in
lemma rational_curve_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B A C : E) (t a c : ℝ) (ht : 0≤t) (ha : 0≤a) (hc : c≤3/4)
    (hA : ‖A‖≤2*c*a) (hC : ‖C-a^2 • B‖≤2*a^2) :
    ‖(1+t^2*a^2)⁻¹ • (B+t • A+t^2 • C)-B‖≤2*t*a := by
  have hd : 0<1+t^2*a^2 := by positivity
  rw [rational_curve_difference B A C t a hd.ne']
  calc
    _ = (1+t^2*a^2)⁻¹*‖t • A+t^2 • (C-a^2 • B)‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hd)]
    _ ≤ (1+t^2*a^2)⁻¹*(t*‖A‖+t^2*‖C-a^2 • B‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hd.le)
      have htn : ‖t‖=t := Real.norm_of_nonneg ht
      have hsn : ‖(t^(2:ℕ):ℝ)‖=t^(2:ℕ) := Real.norm_of_nonneg (sq_nonneg t)
      simpa only [norm_smul,htn,hsn] using
        norm_add_le (t • A) ((t^(2:ℕ)) • (C-a^2 • B))
    _ ≤ (1+t^2*a^2)⁻¹*(t*(2*c*a)+t^2*(2*a^2)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hA ht)
          (mul_le_mul_of_nonneg_left hC (sq_nonneg t))) (inv_nonneg.2 hd.le)
    _ ≤ 2*t*a := by
      apply (inv_mul_le_iff₀ hd).2
      have hx : 0≤t*a := mul_nonneg ht ha
      have hq : c+t*a≤1+(t*a)^2 := by nlinarith [sq_nonneg (t*a-1/2)]
      have hh := mul_le_mul_of_nonneg_left hq (show 0≤2*(t*a) by positivity)
      nlinarith

lemma frobenius_norm_eq_coefficientVector {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (Z : Matrix A B ℂ) :
    ‖Z‖=‖coefficientVector Z‖ := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [←coefficientVector_norm_sq,←Real.sqrt_eq_rpow,Real.sqrt_sq (norm_nonneg _)]

lemma frobenius_norm_one {r : ℕ} : ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖=Real.sqrt r := by
  have h := Matrix.frobenius_nnnorm_one (n := Fin r) (α := ℂ)
  simpa only [Fintype.card_fin,nnnorm_one,mul_one,Real.coe_sqrt,NNReal.coe_natCast] using
    congrArg (fun q : ℝ≥0 => (q : ℝ)) h

lemma inverse_sqrt_le_three_quarters {r : ℕ} (hr : 2≤r) : (Real.sqrt r)⁻¹≤3/4 := by
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hs := Real.sq_sqrt (show (0:ℝ)≤r by positivity)
  have hs0 : 0<Real.sqrt r := Real.sqrt_pos.2 (by positivity)
  have hlow : (4/3:ℝ)≤Real.sqrt r := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [←one_div]
  apply (div_le_iff₀ hs0).2
  linarith

set_option backward.isDefEq.respectTransparency false in
lemma flat_rational_frobenius_le {r : ℕ} (hr : 2≤r)
    (Z : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (ht : 0≤t) :
    ‖(1+t^2*‖Z‖^2)⁻¹ •
      (((r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ))+
        t • ((Real.sqrt r)⁻¹ • (Z+Zᴴ))+t^2 • (Z*Zᴴ))-
        (r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ)‖≤2*t*‖Z‖ := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hc0 : 0≤(Real.sqrt r)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hc := inverse_sqrt_le_three_quarters hr
  have hB : ‖(r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ)‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hr0),frobenius_norm_one]
    have hsq := Real.sq_sqrt hr0.le
    have hs0 : 0<Real.sqrt r := Real.sqrt_pos.2 hr0
    have he : (r:ℝ)⁻¹*Real.sqrt r=(Real.sqrt r)⁻¹ := by
      field_simp
      nlinarith
    rw [he]
    linarith
  apply rational_curve_norm_le _ _ _ t ‖Z‖ (Real.sqrt r)⁻¹ ht (norm_nonneg _) hc
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc0]
    have hZ := norm_add_le Z Zᴴ
    rw [Matrix.frobenius_norm_conjTranspose] at hZ
    calc
      _ ≤ (Real.sqrt r)⁻¹*(‖Z‖+‖Z‖) := mul_le_mul_of_nonneg_left hZ hc0
      _ = _ := by ring
  · calc
      _ ≤ ‖Z*Zᴴ‖+‖‖Z‖^2 • ((r:ℝ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ))‖ := norm_sub_le _ _
      _ ≤ ‖Z‖*‖Zᴴ‖+‖Z‖^2*1 := by
        apply add_le_add (Matrix.frobenius_norm_mul Z Zᴴ)
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left hB (sq_nonneg _)
      _ = _ := by rw [Matrix.frobenius_norm_conjTranspose]; ring

end Cloning.PCTPurity
