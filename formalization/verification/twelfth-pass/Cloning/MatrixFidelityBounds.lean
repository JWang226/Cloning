import Cloning.MatrixFidelity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! # Concrete matrix trace estimates

These estimates concern complex matrices and their positive square roots.
They do not assume a fidelity-continuity axiom or an abstract fidelity law.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Flattening a complex matrix into its Hilbert--Schmidt vector. -/
def hilbertSchmidtVector (A : Matrix m n ℂ) : EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

lemma inner_hilbertSchmidtVector (A B : Matrix m n ℂ) :
    inner ℂ (hilbertSchmidtVector A) (hilbertSchmidtVector B) =
      (A.conjTranspose * B).trace := by
  simp only [hilbertSchmidtVector, EuclideanSpace.inner_toLp_toLp,
    dotProduct, Pi.star_apply, Matrix.trace,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- The squared Hilbert--Schmidt norm is the trace of the Gram matrix. -/
lemma norm_hilbertSchmidtVector_sq (A : Matrix m n ℂ) :
    ‖hilbertSchmidtVector A‖ ^ 2 = (A.conjTranspose * A).trace.re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_hilbertSchmidtVector]
  rfl

/-- Cauchy--Schwarz for matrix traces, with no positivity assumptions. -/
theorem trace_cauchy_schwarz_sq (A B : Matrix m n ℂ) :
    ‖(A.conjTranspose * B).trace‖ ^ 2 ≤
      (A.conjTranspose * A).trace.re * (B.conjTranspose * B).trace.re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hilbertSchmidtVector A) (hilbertSchmidtVector B)
  have hsq := mul_self_le_mul_self (norm_nonneg _) h
  rw [inner_hilbertSchmidtVector] at hsq
  rw [← norm_hilbertSchmidtVector_sq A, ← norm_hilbertSchmidtVector_sq B]
  nlinarith

/-- The real trace version of Hilbert--Schmidt Cauchy--Schwarz. -/
theorem re_trace_cauchy_schwarz_sq (A B : Matrix m n ℂ) :
    (A.conjTranspose * B).trace.re ^ 2 ≤
      (A.conjTranspose * A).trace.re * (B.conjTranspose * B).trace.re := by
  have h := trace_cauchy_schwarz_sq A B
  have he := Complex.sq_norm_sub_sq_re ((A.conjTranspose * B).trace)
  nlinarith [sq_nonneg ((A.conjTranspose * B).trace.im)]

variable [DecidableEq n]

/-- A dimension-dependent square-root trace bound, derived directly from
matrix Cauchy--Schwarz and the positive-square-root identity. -/
theorem sqrt_trace_sq_le_card_mul_trace (A : Matrix n n ℂ)
    (hA : A.PosSemidef) :
    (CFC.sqrt A).trace.re ^ 2 ≤ (Fintype.card n : ℝ) * A.trace.re := by
  have h := re_trace_cauchy_schwarz_sq (1 : Matrix n n ℂ) (CFC.sqrt A)
  have hS : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hs : (CFC.sqrt A).conjTranspose * CFC.sqrt A = A := by
    rw [hS.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  simpa only [Matrix.conjTranspose_one, one_mul, hs, Matrix.trace_one,
    Complex.natCast_re] using h

/-- The unsquared dimension-dependent bound. -/
theorem sqrt_trace_le_sqrt_card_mul_trace (A : Matrix n n ℂ)
    (hA : A.PosSemidef) :
    (CFC.sqrt A).trace.re ≤ Real.sqrt ((Fintype.card n : ℝ) * A.trace.re) := by
  have h := sqrt_trace_sq_le_card_mul_trace A hA
  have hn : 0 ≤ (Fintype.card n : ℝ) * A.trace.re :=
    mul_nonneg (Nat.cast_nonneg _) hA.trace_nonneg.1
  have hs := Real.sq_sqrt hn
  have hs0 := Real.sqrt_nonneg ((Fintype.card n : ℝ) * A.trace.re)
  nlinarith

section Continuity

open scoped Matrix.Norms.L2Operator

local instance : CStarAlgebra (Matrix n n ℂ) where

/-- Positive matrix square roots depend continuously on the matrix within
the positive cone, for each fixed finite matrix dimension. -/
theorem continuousOn_matrix_sqrt :
    ContinuousOn (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ)
      {A | A.PosSemidef} := by
  simpa only [Matrix.nonneg_iff_posSemidef] using
    (CFC.continuousOn_sqrt (A := Matrix n n ℂ))

/-- Actual finite-dimensional root fidelity is jointly continuous on the
positive cone. This is qualitative fixed-dimension continuity, not the
dimension-independent trace-norm modulus needed for LAN. -/
theorem continuousOn_fidelity :
    ContinuousOn (fun p : Matrix n n ℂ × Matrix n n ℂ => fidelity p.1 p.2)
      {p | p.1.PosSemidef ∧ p.2.PosSemidef} := by
  have hB : ContinuousOn
      (fun p : Matrix n n ℂ × Matrix n n ℂ => CFC.sqrt p.2)
      {p | p.1.PosSemidef ∧ p.2.PosSemidef} :=
    continuousOn_matrix_sqrt.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hinside := (hB.mul continuous_fst.continuousOn).mul hB
  have hout := continuousOn_matrix_sqrt.comp hinside
    (fun p hp => sandwich_posSemidef hp.1 p.2)
  have htrace : Continuous (fun A : Matrix n n ℂ => A.trace.re) := by
    unfold Matrix.trace
    fun_prop
  exact htrace.comp_continuousOn hout

end Continuity

end Cloning.MatrixFidelity
