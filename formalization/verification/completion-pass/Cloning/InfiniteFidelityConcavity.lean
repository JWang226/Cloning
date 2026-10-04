import Cloning.InfiniteChannelFidelity

/-! Joint concavity of root fidelity for actual positive trace-class
operators, obtained by combining attaining positive-block witnesses. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace Cloning.InfiniteFidelity
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weighted joint superadditivity, with arbitrary nonnegative weights.
The normalized-weight case is joint concavity. -/
theorem fidelity_weighted_joint_concavity
    (A B C D : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1)
    (hC : 0 ≤ C.1) (hD : 0 ≤ D.1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * fidelity A.1 B.1 hA hB A.2 B.2 +
      b * fidelity C.1 D.1 hC hD C.2 D.2 ≤
        fidelity (((a : ℂ) • A + (b : ℂ) • C).1)
          (((a : ℂ) • B + (b : ℂ) • D).1)
          (add_nonneg (smul_nonneg (by exact_mod_cast ha) hA)
            (smul_nonneg (by exact_mod_cast hb) hC))
          (add_nonneg (smul_nonneg (by exact_mod_cast ha) hB)
            (smul_nonneg (by exact_mod_cast hb) hD))
          ((a : ℂ) • A + (b : ℂ) • C).2 ((a : ℂ) • B + (b : ℂ) • D).2 := by
  obtain ⟨X, hX, htX⟩ := exists_fidelityBlock_witness A B hA hB
  obtain ⟨Y, hY, htY⟩ := exists_fidelityBlock_witness C D hC hD
  have hblock (x y : H) :
      0 ≤ ⟪x, (((a : ℂ) • A + (b : ℂ) • C).1) x⟫_ℂ +
        ⟪x, (((a : ℂ) • X + (b : ℂ) • Y).1) y⟫_ℂ +
        ⟪y, (star (((a : ℂ) • X + (b : ℂ) • Y).1)) x⟫_ℂ +
        ⟪y, (((a : ℂ) • B + (b : ℂ) • D).1) y⟫_ℂ := by
    have hx := fidelityBlock_quadratic A B X hX x y
    have hy := fidelityBlock_quadratic C D Y hY x y
    have hca : (0 : ℂ) ≤ (a : ℂ) := by exact_mod_cast ha
    have hcb : (0 : ℂ) ≤ (b : ℂ) := by exact_mod_cast hb
    have hn := add_nonneg (mul_nonneg hca hx) (mul_nonneg hcb hy)
    convert hn using 1
    change ⟪x, ((a : ℂ) • A.1 + (b : ℂ) • C.1) x⟫_ℂ +
      ⟪x, ((a : ℂ) • X.1 + (b : ℂ) • Y.1) y⟫_ℂ +
      ⟪y, (star ((a : ℂ) • X.1 + (b : ℂ) • Y.1)) x⟫_ℂ +
      ⟪y, ((a : ℂ) • B.1 + (b : ℂ) • D.1) y⟫_ℂ =
        (a : ℂ) * _ + (b : ℂ) * _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right, star_add, star_smul,
      Complex.star_def, Complex.conj_ofReal]
    ring
  have h := trace_re_le_fidelity_of_block ((a : ℂ) • A + (b : ℂ) • C)
    ((a : ℂ) • B + (b : ℂ) • D) ((a : ℂ) • X + (b : ℂ) • Y)
    (add_nonneg (smul_nonneg (by exact_mod_cast ha) hA)
      (smul_nonneg (by exact_mod_cast hb) hC))
    (add_nonneg (smul_nonneg (by exact_mod_cast ha) hB)
      (smul_nonneg (by exact_mod_cast hb) hD)) hblock
  simpa only [map_add, map_smul, smul_eq_mul, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, htX, htY] using h

end Cloning.InfiniteFidelity
