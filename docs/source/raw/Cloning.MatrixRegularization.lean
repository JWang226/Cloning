import Cloning.MatrixFidelityBounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Positive-definite regularization of positive complex matrices

The regularization is the concrete matrix `A + ε I`. Its positivity, strict
positivity, traces, limits, and inverse square-root identities are proved here.
-/

noncomputable section

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix Filter
open Cloning.MatrixFidelity

namespace Cloning.MatrixRegularization

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Addition of scalar white noise to a positive matrix. -/
def regularize (A : Matrix n n ℂ) (ε : ℝ) : Matrix n n ℂ := A + ε • 1

omit [Fintype n] in
theorem regularize_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) : (regularize A ε).PosSemidef :=
  hA.add (Matrix.PosSemidef.one.smul hε)

omit [Fintype n] in
theorem regularize_posDef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) : (regularize A ε).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)

omit [Fintype n] in
theorem le_regularize (A : Matrix n n ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    A ≤ regularize A ε := by
  exact le_add_of_nonneg_right (Matrix.PosSemidef.one.smul hε).nonneg

theorem regularize_trace (A : Matrix n n ℂ) (ε : ℝ) :
    (regularize A ε).trace = A.trace + (ε : ℂ) * (Fintype.card n : ℂ) := by
  simp [regularize, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]

theorem regularize_trace_re (A : Matrix n n ℂ) (ε : ℝ) :
    (regularize A ε).trace.re = A.trace.re + ε * (Fintype.card n : ℝ) := by
  rw [regularize_trace]
  simp

omit [Fintype n] in
theorem continuous_regularize (A : Matrix n n ℂ) : Continuous (regularize A) := by
  unfold regularize
  fun_prop

omit [Fintype n] in
theorem tendsto_regularize_zero (A : Matrix n n ℂ) :
    Tendsto (regularize A) (nhds 0) (nhds A) := by
  simpa [regularize] using (continuous_regularize A).tendsto 0

omit [Fintype n] in
theorem tendsto_regularize_pos (A : Matrix n n ℂ) :
    Tendsto (regularize A) (nhdsWithin 0 (Set.Ioi 0)) (nhds A) :=
  (tendsto_regularize_zero A).mono_left inf_le_left

/-- The positive square root of a positive-definite matrix is invertible. -/
theorem sqrt_isUnit {A : Matrix n n ℂ} (hA : A.PosDef) : IsUnit (CFC.sqrt A) :=
  hA.isStrictlyPositive.sqrt.posDef.isUnit

theorem sqrt_mul_inv {A : Matrix n n ℂ} (hA : A.PosDef) :
    CFC.sqrt A * (CFC.sqrt A)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt A)).mp (sqrt_isUnit hA))

theorem sqrt_inv_mul {A : Matrix n n ℂ} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * CFC.sqrt A = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt A)).mp (sqrt_isUnit hA))

theorem sqrt_inv_posDef {A : Matrix n n ℂ} (hA : A.PosDef) :
    ((CFC.sqrt A)⁻¹).PosDef := hA.isStrictlyPositive.sqrt.posDef.inv

theorem sqrt_inv_conjTranspose (A : Matrix n n ℂ) :
    ((CFC.sqrt A)⁻¹)ᴴ = (CFC.sqrt A)⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, sqrt_conjTranspose]

theorem sqrt_inv_square {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ := by
  rw [← sq, Matrix.inv_pow', CFC.sq_sqrt A hA.nonneg]

/-- Inverse square roots undo the positive sandwich of a positive-definite matrix. -/
theorem sqrt_inv_sandwich {A : Matrix n n ℂ} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * A * (CFC.sqrt A)⁻¹ = 1 := by
  calc
    (CFC.sqrt A)⁻¹ * A * (CFC.sqrt A)⁻¹ =
        (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A)⁻¹ := by
      rw [sqrt_mul_self hA.posSemidef]
    _ = ((CFC.sqrt A)⁻¹ * CFC.sqrt A) * (CFC.sqrt A * (CFC.sqrt A)⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [sqrt_inv_mul hA, sqrt_mul_inv hA, Matrix.one_mul]

/-- A general limit lemma for the trace of the positive square root along the
positive cone. It is useful when removing a positive-definite regularization. -/
theorem tendsto_trace_sqrt {ι : Type*} {l : Filter ι} {A : Matrix n n ℂ}
    {f : ι → Matrix n n ℂ} (hA : A.PosSemidef)
    (hf : Tendsto f l (nhds A)) (hpos : ∀ᶠ i in l, (f i).PosSemidef) :
    Tendsto (fun i => (CFC.sqrt (f i)).trace.re) l (nhds (CFC.sqrt A).trace.re) := by
  have hin : Tendsto f l (nhdsWithin A {X : Matrix n n ℂ | X.PosSemidef}) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf, hpos⟩
  have hs : Tendsto (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ)
      (nhdsWithin A {X : Matrix n n ℂ | X.PosSemidef}) (nhds (CFC.sqrt A)) :=
    continuousOn_matrix_sqrt A hA
  have ht : Continuous (fun X : Matrix n n ℂ => X.trace.re) := by
    unfold Matrix.trace
    fun_prop
  exact ht.continuousAt.tendsto.comp (hs.comp hin)

theorem tendsto_trace_sqrt_regularize {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Tendsto (fun ε => (CFC.sqrt (regularize A ε)).trace.re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (CFC.sqrt A).trace.re) := by
  apply tendsto_trace_sqrt hA (tendsto_regularize_pos A)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact regularize_posSemidef hA hε.le

end Cloning.MatrixRegularization
