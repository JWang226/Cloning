import Cloning.MatrixFidelityBlockBound
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith

/-!
# Weighted root-fidelity bounds for finite complex matrices

For positive matrices `A`, `B` and a positive-definite matrix weight `W`,
the squared root fidelity is bounded by `Re tr(A W) * Re tr(B W⁻¹)`.
The weight need not commute with either input. All operators here are finite
matrices; no statement about unbounded infinite-dimensional weights is made.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Topology
open Matrix Filter

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pairing the positive block quadratic with the inverse weight gives a
nonnegative real quadratic for every real scalar, including negative ones. -/
theorem block_weighted_quadratic_nonneg {A B X W : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef) (hW : W.PosDef)
    (s : ℝ) :
    0 ≤ (Matrix.trace (A * W)).re * (s * s) +
      (-2 * (Matrix.trace X).re) * s + (Matrix.trace (B * W⁻¹)).re := by
  have hsW : (s • W).IsHermitian := by
    change (s • W)ᴴ = s • W
    simp only [Matrix.conjTranspose_smul, hW.isHermitian.eq, star_trivial]
  have hQ := block_quadratic_posSemidef hblock hsW
  have hpair := trace_mul_re_nonneg hQ hW.inv.posSemidef
  have hWi : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hW.isUnit
  have hfirst : Matrix.trace (W * A * W * W⁻¹) = Matrix.trace (A * W) := by
    rw [Matrix.mul_assoc (W * A) W W⁻¹, Matrix.mul_nonsing_inv W hWi,
      Matrix.mul_one, Matrix.trace_mul_comm W A]
  have hsecond : Matrix.trace (W * X * W⁻¹) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul W hWi, Matrix.one_mul]
  have hthird : Matrix.trace (Xᴴ * W * W⁻¹) = star (Matrix.trace X) := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv W hWi,
      Matrix.mul_one, Matrix.trace_conjTranspose]
  simp only [Matrix.add_mul, Matrix.sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] at hpair
  rw [hfirst, hsecond, hthird] at hpair
  have hstar : (star (Matrix.trace X)).re = (Matrix.trace X).re := rfl
  rw [hstar] at hpair
  nlinarith only [hpair]

/-- The scalar discriminant controls the off-diagonal trace of every
positive block matrix by the two weighted diagonal traces. -/
theorem block_trace_sq_le_weighted_trace_product {A B X W : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef) (hW : W.PosDef) :
    (Matrix.trace X).re ^ 2 ≤
      (Matrix.trace (A * W)).re * (Matrix.trace (B * W⁻¹)).re := by
  have h := discrim_le_zero (block_weighted_quadratic_nonneg hblock hW)
  unfold discrim at h
  nlinarith only [h]

/-- The weighted inequality for positive-definite inputs follows from an
explicit feasible block whose off-diagonal trace attains root fidelity. -/
theorem fidelity_sq_le_weighted_trace_product_posDef {A B W : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hW : W.PosDef) :
    fidelity A B ^ 2 ≤
      (Matrix.trace (A * W)).re * (Matrix.trace (B * W⁻¹)).re := by
  obtain ⟨X, hblock, htrace⟩ := exists_fidelity_block_witness hA hB
  simpa only [htrace] using block_trace_sq_le_weighted_trace_product hblock hW

/-- The noncommutative weighted root-fidelity inequality for arbitrary
positive finite matrices and any positive-definite finite matrix weight.
The inputs may be singular and need not have unit trace. -/
theorem fidelity_sq_le_weighted_trace_product {A B W : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hW : W.PosDef) :
    fidelity A B ^ 2 ≤
      (Matrix.trace (A * W)).re * (Matrix.trace (B * W⁻¹)).re := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  let Aseq := fun k => Cloning.MatrixRegularization.regularize A (ε k)
  let Bseq := fun k => Cloning.MatrixRegularization.regularize B (ε k)
  have hAseq (k : ℕ) : (Aseq k).PosDef :=
    Cloning.MatrixRegularization.regularize_posDef hA (hε k)
  have hBseq (k : ℕ) : (Bseq k).PosDef :=
    Cloning.MatrixRegularization.regularize_posDef hB (hε k)
  have hAlim : Tendsto Aseq atTop (𝓝 A) :=
    (Cloning.MatrixRegularization.tendsto_regularize_zero A).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hBlim : Tendsto Bseq atTop (𝓝 B) :=
    (Cloning.MatrixRegularization.tendsto_regularize_zero B).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft := (tendsto_fidelity hA hB (fun k => (hAseq k).posSemidef)
    (fun k => (hBseq k).posSemidef) hAlim hBlim).pow 2
  have htrace (V : Matrix n n ℂ) :
      Continuous (fun C : Matrix n n ℂ => (Matrix.trace (C * V)).re) := by
    unfold Matrix.trace
    fun_prop
  have hright := ((htrace W).continuousAt.tendsto.comp hAlim).mul
    ((htrace W⁻¹).continuousAt.tendsto.comp hBlim)
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall (fun k =>
    fidelity_sq_le_weighted_trace_product_posDef (hAseq k) (hBseq k) hW)

end Cloning.MatrixFidelity
