import Cloning.MatrixFidelityBounds
import Cloning.MatrixRegularization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Dimension-independent trace bound for concrete root fidelity

The invertible case follows from a matrix factorization and Hilbert--Schmidt
Cauchy--Schwarz. Singular positive matrices are treated by regularization.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix Filter
open scoped Topology

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Dimension-independent trace bound when the second positive matrix is
invertible. The first matrix may have a nontrivial kernel. -/
theorem fidelity_sq_le_trace_mul_trace_of_isUnit
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hBu : IsUnit B) :
    fidelity A B ^ 2 ≤ A.trace.re * B.trace.re := by
  let C := CFC.sqrt B
  let R := CFC.sqrt (C * A * C)
  let D := C⁻¹ * R
  have hCu : IsUnit C := (CFC.isUnit_sqrt_iff B hB.nonneg).mpr hBu
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCu
  have hCV : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCd
  have hVC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hCd
  have hCstar : Cᴴ = C := sqrt_conjTranspose B
  have hRstar : Rᴴ = R := sqrt_conjTranspose (C * A * C)
  have hVstar : C⁻¹ᴴ = C⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hCstar]
  have hCC : Cᴴ * C = B := by
    rw [hCstar]
    exact sqrt_mul_self hB
  have hRR : R * R = C * A * C :=
    sqrt_mul_self (sandwich_posSemidef hA B)
  have hCD : Cᴴ * D = R := by
    dsimp [D]
    rw [hCstar, ← Matrix.mul_assoc, hCV, one_mul]
  have hDD : (Dᴴ * D).trace = A.trace := by
    dsimp [D]
    rw [Matrix.conjTranspose_mul, hRstar, hVstar]
    calc
      ((R * C⁻¹) * (C⁻¹ * R)).trace = ((C⁻¹ * R) * (R * C⁻¹)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (C⁻¹ * (R * R) * C⁻¹).trace := by
        simp only [Matrix.mul_assoc]
      _ = (C⁻¹ * (C * A * C) * C⁻¹).trace := by rw [hRR]
      _ = ((C⁻¹ * C) * A * (C * C⁻¹)).trace := by
        simp only [Matrix.mul_assoc]
      _ = A.trace := by rw [hVC, hCV, one_mul, mul_one]
  have h := re_trace_cauchy_schwarz_sq C D
  rw [hCD, hCC, hDD] at h
  simpa only [fidelity, C, R, mul_comm] using h

/-- Concrete fidelity is continuous along positive matrix approximations
in its second argument. -/
theorem tendsto_fidelity_right
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {Bseq : ℕ → Matrix n n ℂ} (hseq : ∀ k, (Bseq k).PosSemidef)
    (hlim : Tendsto Bseq atTop (𝓝 B)) :
    Tendsto (fun k => fidelity A (Bseq k)) atTop (𝓝 (fidelity A B)) := by
  have hin : Tendsto Bseq atTop (𝓝[{X | X.PosSemidef}] B) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hseq⟩
  have hsqrt : Tendsto (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ)
      (𝓝[{X | X.PosSemidef}] B) (𝓝 (CFC.sqrt B)) :=
    continuousOn_matrix_sqrt B hB
  have hS : Tendsto (fun k => CFC.sqrt (Bseq k)) atTop (𝓝 (CFC.sqrt B)) :=
    hsqrt.comp hin
  have hprod : Tendsto (fun k => CFC.sqrt (Bseq k) * A * CFC.sqrt (Bseq k))
      atTop (𝓝 (CFC.sqrt B * A * CFC.sqrt B)) := (hS.mul_const A).mul hS
  exact Cloning.MatrixRegularization.tendsto_trace_sqrt
    (sandwich_posSemidef hA B) hprod
    (Filter.Eventually.of_forall (fun k => sandwich_posSemidef hA (Bseq k)))

/-- The trace estimate survives singular limits of positive invertible
matrices. -/
theorem fidelity_sq_le_trace_mul_trace_of_approximants
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (Bseq : ℕ → Matrix n n ℂ) (hseq : ∀ k, (Bseq k).PosSemidef)
    (hseqUnit : ∀ k, IsUnit (Bseq k)) (hlim : Tendsto Bseq atTop (𝓝 B)) :
    fidelity A B ^ 2 ≤ A.trace.re * B.trace.re := by
  have hf := (tendsto_fidelity_right hA hB hseq hlim).pow 2
  have htrace : Continuous (fun X : Matrix n n ℂ => X.trace.re) := by
    unfold Matrix.trace
    fun_prop
  have ht := (tendsto_const_nhds (x := A.trace.re)).mul
    (htrace.continuousAt.tendsto.comp hlim)
  apply le_of_tendsto_of_tendsto hf ht
  exact Filter.Eventually.of_forall (fun k =>
    fidelity_sq_le_trace_mul_trace_of_isUnit hA (hseq k) (hseqUnit k))

/-- Dimension-independent Cauchy--Schwarz bound for arbitrary positive
matrices, including singular and zero matrices. -/
theorem fidelity_sq_le_trace_mul_trace
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A B ^ 2 ≤ A.trace.re * B.trace.re := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  let Bseq := fun k => Cloning.MatrixRegularization.regularize B (ε k)
  have hseqPD (k : ℕ) : (Bseq k).PosDef :=
    Cloning.MatrixRegularization.regularize_posDef hB (hε k)
  apply fidelity_sq_le_trace_mul_trace_of_approximants hA hB Bseq
    (fun k => (hseqPD k).posSemidef) (fun k => (hseqPD k).isUnit)
  exact (Cloning.MatrixRegularization.tendsto_regularize_zero B).comp
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The usual root-fidelity trace bound, proved for concrete complex
matrices without assumptions about fidelity laws. -/
theorem fidelity_le_sqrt_trace_mul_trace
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A B ≤ Real.sqrt (A.trace.re * B.trace.re) := by
  have hsq := fidelity_sq_le_trace_mul_trace hA hB
  have ht : 0 ≤ A.trace.re * B.trace.re :=
    mul_nonneg (trace_re_nonneg hA) (trace_re_nonneg hB)
  have hs := Real.sq_sqrt ht
  have hs0 := Real.sqrt_nonneg (A.trace.re * B.trace.re)
  nlinarith

/-- Fidelity between concrete subnormalized positive matrices is at most one. -/
theorem fidelity_le_one
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrA : A.trace.re ≤ 1) (htrB : B.trace.re ≤ 1) : fidelity A B ≤ 1 := by
  have h := fidelity_sq_le_trace_mul_trace hA hB
  have htrA0 := trace_re_nonneg hA
  have htrB0 := trace_re_nonneg hB
  have hm : A.trace.re * B.trace.re ≤ 1 := by nlinarith
  nlinarith

end Cloning.MatrixFidelity
