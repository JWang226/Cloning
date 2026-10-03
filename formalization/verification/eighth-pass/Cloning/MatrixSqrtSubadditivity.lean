import Cloning.MatrixFidelity
import Cloning.MatrixTraceOrder
import Cloning.MatrixRegularization
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Subadditivity of the trace of the positive square root

The positive definite estimate follows by comparison of inverse square roots.
The positive semidefinite extension is obtained by regularization and continuity.
No trace-norm triangle inequality or fidelity law is assumed.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Filter Cloning.MatrixRegularization
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance matrixSqrtSubadditivityCStarAlgebra : CStarAlgebra (Matrix n n ℂ) where

/-- Cancellation with the inverse positive square root of a positive definite
matrix, using the concrete nonsingular matrix inverse. -/
lemma mul_inv_sqrt_eq_sqrt {X : Matrix n n ℂ} (hX : X.PosDef) :
    X * (CFC.sqrt X)⁻¹ = CFC.sqrt X := by
  have hS : (CFC.sqrt X).PosDef := hX.isStrictlyPositive.sqrt.posDef
  have hdet : IsUnit (CFC.sqrt X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  calc
    X * (CFC.sqrt X)⁻¹ = (CFC.sqrt X * CFC.sqrt X) * (CFC.sqrt X)⁻¹ := by
      rw [sqrt_mul_self hX.posSemidef]
    _ = CFC.sqrt X := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

/-- Subadditivity of the square-root trace for positive definite matrices. -/
lemma trace_sqrt_add_le_posDef {X Y : Matrix n n ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) :
    (Matrix.trace (CFC.sqrt (X + Y))).re ≤
      (Matrix.trace (CFC.sqrt X)).re + (Matrix.trace (CFC.sqrt Y)).re := by
  have hS : (X + Y).PosDef := hX.add hY
  have hXS : X ≤ X + Y := le_add_of_nonneg_right hY.posSemidef.nonneg
  have hYS : Y ≤ X + Y := le_add_of_nonneg_left hX.posSemidef.nonneg
  calc
    (Matrix.trace (CFC.sqrt (X + Y))).re =
        (Matrix.trace ((X + Y) * (CFC.sqrt (X + Y))⁻¹)).re := by
      rw [mul_inv_sqrt_eq_sqrt hS]
    _ = (Matrix.trace (X * (CFC.sqrt (X + Y))⁻¹)).re +
        (Matrix.trace (Y * (CFC.sqrt (X + Y))⁻¹)).re := by
      rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    _ ≤ (Matrix.trace (X * (CFC.sqrt X)⁻¹)).re +
        (Matrix.trace (Y * (CFC.sqrt Y)⁻¹)).re :=
      add_le_add
        (trace_mul_re_mono_right hX.posSemidef (sqrt_inv_antitone hX hS hXS))
        (trace_mul_re_mono_right hY.posSemidef (sqrt_inv_antitone hY hS hYS))
    _ = _ := by rw [mul_inv_sqrt_eq_sqrt hX, mul_inv_sqrt_eq_sqrt hY]

/-- Subadditivity of the trace of the positive square root, including singular
positive semidefinite matrices. The proof removes strictly positive white-noise
regularization by continuity along the positive cone. -/
theorem trace_sqrt_add_le {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (Matrix.trace (CFC.sqrt (X + Y))).re ≤
      (Matrix.trace (CFC.sqrt X)).re + (Matrix.trace (CFC.sqrt Y)).re := by
  have hSum : Tendsto
      (fun ε => (CFC.sqrt (regularize X ε + regularize Y ε)).trace.re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (CFC.sqrt (X + Y)).trace.re) := by
    apply tendsto_trace_sqrt (hX.add hY)
      ((tendsto_regularize_pos X).add (tendsto_regularize_pos Y))
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (regularize_posSemidef hX hε.le).add (regularize_posSemidef hY hε.le)
  exact le_of_tendsto_of_tendsto hSum
    ((tendsto_trace_sqrt_regularize hX).add (tendsto_trace_sqrt_regularize hY))
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact trace_sqrt_add_le_posDef (regularize_posDef hX hε) (regularize_posDef hY hε))
end Cloning.MatrixFidelity
