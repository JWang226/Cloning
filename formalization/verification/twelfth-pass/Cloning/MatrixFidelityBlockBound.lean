import Cloning.MatrixTraceOrder
import Cloning.MatrixFidelitySymmetry
import Cloning.MatrixFidelityWitness
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Linarith

/-!
# Positive block matrices bound root fidelity

A positive block matrix with diagonal blocks `A`, `B` and off-diagonal block
`X` satisfies `Re (trace X) ≤ fidelity A B`. The proof uses a positive-definite
trace-pairing bound and then removes strict positivity by regularization.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Topology
open Matrix Filter

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Testing a positive block matrix against the column `(H, -I)` gives a
positive matrix even when the blocks do not commute. -/
theorem block_quadratic_posSemidef {A B X H : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef)
    (hH : H.IsHermitian) :
    (H * A * H - H * X - Xᴴ * H + B).PosSemidef := by
  have h := hblock.conjTranspose_mul_mul_same (Matrix.fromRows H (-1))
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    hH.eq, Matrix.conjTranspose_neg, Matrix.conjTranspose_one,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows] at h
  simpa only [neg_mul, one_mul, mul_neg, mul_one, add_mul,
    add_neg_cancel_right, sub_eq_add_neg, neg_add_rev, neg_neg,
    add_assoc, add_left_comm, add_comm] using h

/-- Every positive-definite weight gives the weighted arithmetic upper bound
on the real off-diagonal trace of a positive block matrix. -/
theorem block_trace_weighted_bound {A B X H : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef)
    (hH : H.PosDef) :
    2 * (Matrix.trace X).re ≤
      (Matrix.trace (A * H)).re + (Matrix.trace (B * H⁻¹)).re := by
  have hQ := block_quadratic_posSemidef hblock hH.isHermitian
  have hpair := trace_mul_re_nonneg hQ hH.inv.posSemidef
  have hHi : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hmul : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hHi
  have hfirst : Matrix.trace (H * A * H * H⁻¹) = Matrix.trace (A * H) := by
    rw [Matrix.mul_assoc (H * A) H H⁻¹, hmul, Matrix.mul_one,
      Matrix.trace_mul_comm H A]
  have hsecond : Matrix.trace (H * X * H⁻¹) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul H hHi, Matrix.one_mul]
  have hthird : Matrix.trace (Xᴴ * H * H⁻¹) = star (Matrix.trace X) := by
    rw [Matrix.mul_assoc, hmul, Matrix.mul_one, Matrix.trace_conjTranspose]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re] at hpair
  rw [hfirst, hsecond, hthird] at hpair
  have hstar : (star (Matrix.trace X)).re = (Matrix.trace X).re := rfl
  rw [hstar] at hpair
  linarith

/-- At an optimal positive-definite weight the two weighted trace terms
coincide, so the off-diagonal trace is bounded by root fidelity. -/
theorem trace_re_le_fidelity_of_block_and_witness {A B X H : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef)
    (hH : H.PosDef) (hHAH : H * A * H = B)
    (hoptimal : (Matrix.trace (A * H)).re = fidelity A B) :
    (Matrix.trace X).re ≤ fidelity A B := by
  have hbound := block_trace_weighted_bound hblock hH
  have hHi : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hterm : Matrix.trace (B * H⁻¹) = Matrix.trace (A * H) := by
    rw [← hHAH, Matrix.mul_assoc (H * A) H H⁻¹,
      Matrix.mul_nonsing_inv H hHi, Matrix.mul_one, Matrix.trace_mul_comm H A]
  rw [hterm, hoptimal] at hbound
  linarith

omit [Fintype n] in
/-- Scalar regularization of both diagonal blocks preserves positivity
without changing the off-diagonal block. -/
theorem block_regularize_posSemidef {A B X : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Matrix.fromBlocks (Cloning.MatrixRegularization.regularize A ε) X Xᴴ
      (Cloning.MatrixRegularization.regularize B ε)).PosSemidef := by
  have h := Cloning.MatrixRegularization.regularize_posSemidef hblock hε
  have heq : Cloning.MatrixRegularization.regularize (Matrix.fromBlocks A X Xᴴ B) ε =
      Matrix.fromBlocks (Cloning.MatrixRegularization.regularize A ε) X Xᴴ
        (Cloning.MatrixRegularization.regularize B ε) := by
    unfold Cloning.MatrixRegularization.regularize
    rw [← Matrix.fromBlocks_one (l := n) (m := n), Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    simp only [smul_zero, add_zero]
  rwa [heq] at h

omit [Fintype n] [DecidableEq n] in
/-- The diagonal blocks of a positive block matrix are positive. -/
theorem block_diagonal_posSemidef {A B X : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef) :
    A.PosSemidef ∧ B.PosSemidef :=
  ⟨hblock.submatrix Sum.inl, hblock.submatrix Sum.inr⟩

/-- The block trace bound for positive-definite diagonal blocks, obtained by
constructing the optimal geometric-mean weight. -/
theorem trace_re_le_fidelity_of_block_posSemidef_posDef {A B X : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef)
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef) :
    (Matrix.trace X).re ≤ fidelity A B := by
  obtain ⟨H, hH, hHAH, htrace⟩ := exists_fidelity_witness hA hB
  exact trace_re_le_fidelity_of_block_and_witness hblock hH hHAH htrace

/-- Every positive block matrix bounds its off-diagonal real trace by the
root fidelity of its diagonal blocks. No invertibility or normalization is
assumed; singular diagonal blocks are handled by positive regularization. -/
theorem trace_re_le_fidelity_of_block_posSemidef {A B X : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks A X Xᴴ B).PosSemidef) :
    (Matrix.trace X).re ≤ fidelity A B := by
  obtain ⟨hA, hB⟩ := block_diagonal_posSemidef hblock
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
  have hlim := tendsto_fidelity hA hB (fun k => (hAseq k).posSemidef)
    (fun k => (hBseq k).posSemidef) hAlim hBlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  exact Filter.Eventually.of_forall (fun k =>
    trace_re_le_fidelity_of_block_posSemidef_posDef (hAseq k) (hBseq k)
      (block_regularize_posSemidef hblock (hε k).le))

end Cloning.MatrixFidelity
