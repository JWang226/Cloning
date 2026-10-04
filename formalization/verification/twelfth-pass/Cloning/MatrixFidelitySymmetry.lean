import Cloning.MatrixFidelityTraceBound
import Cloning.MatrixFidelityEmbedding

/-! # Symmetry of concrete finite-dimensional root fidelity

Invertible matrices admit an explicit polar isometry. Trace invariance under
that isometry identifies the two square-root Gram traces. Positive-definite
regularization then removes invertibility without changing matrix dimension.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Topology
open Matrix Filter

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The two Gram matrices of an invertible square matrix have the same
square-root trace, proved using its explicit polar isometry. -/
theorem trace_sqrt_conjTranspose_mul_eq_of_isUnit
    (X : Matrix n n ℂ) (hX : IsUnit X) :
    (CFC.sqrt (Xᴴ * X)).trace = (CFC.sqrt (X * Xᴴ)).trace := by
  let C := CFC.sqrt (Xᴴ * X)
  let V := C⁻¹
  let U := X * V
  have hY : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have hXu : IsUnit Xᴴ := isUnit_star.mpr hX
  have hCu : IsUnit C := (CFC.isUnit_sqrt_iff (Xᴴ * X) hY.nonneg).mpr (hXu.mul hX)
  have hCd := (Matrix.isUnit_iff_isUnit_det C).mp hCu
  have hCV : C * V = 1 := Matrix.mul_nonsing_inv C hCd
  have hVC : V * C = 1 := Matrix.nonsing_inv_mul C hCd
  have hCstar : Cᴴ = C := sqrt_conjTranspose (Xᴴ * X)
  have hVstar : Vᴴ = V := by
    dsimp [V]
    rw [Matrix.conjTranspose_nonsing_inv, hCstar]
  have hCC : C * C = Xᴴ * X := sqrt_mul_self hY
  have hUstar : Uᴴ = V * Xᴴ := by
    dsimp [U]
    rw [Matrix.conjTranspose_mul, hVstar]
  have hU : Uᴴ * U = 1 := by
    rw [hUstar]
    dsimp [U]
    calc
      (V * Xᴴ) * (X * V) = V * (Xᴴ * X) * V := by simp only [Matrix.mul_assoc]
      _ = V * (C * C) * V := by rw [hCC]
      _ = (V * C) * (C * V) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hVC, hCV, one_mul]
  have hconj : U * (Xᴴ * X) * Uᴴ = X * Xᴴ := by
    rw [hUstar]
    dsimp [U]
    calc
      (X * V) * (Xᴴ * X) * (V * Xᴴ) =
          X * (V * (C * C) * V) * Xᴴ := by rw [hCC]; simp only [Matrix.mul_assoc]
      _ = X * ((V * C) * (C * V)) * Xᴴ := by simp only [Matrix.mul_assoc]
      _ = X * Xᴴ := by rw [hVC, hCV, one_mul, mul_one]
  have hs := sqrt_isometric_embedding U hU hY
  rw [hconj] at hs
  rw [hs, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, one_mul]

/-- Symmetry when both positive matrices are invertible. -/
theorem fidelity_symm_of_isUnit {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAu : IsUnit A) (hBu : IsUnit B) :
    fidelity A B = fidelity B A := by
  let X := CFC.sqrt A * CFC.sqrt B
  have hX : IsUnit X :=
    ((CFC.isUnit_sqrt_iff A hA.nonneg).mpr hAu).mul
      ((CFC.isUnit_sqrt_iff B hB.nonneg).mpr hBu)
  have hXY : Xᴴ * X = CFC.sqrt B * A * CFC.sqrt B := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, sqrt_conjTranspose]
    calc
      (CFC.sqrt B * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt B) =
          CFC.sqrt B * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt B := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_mul_self hA]
  have hYX : X * Xᴴ = CFC.sqrt A * B * CFC.sqrt A := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, sqrt_conjTranspose]
    calc
      (CFC.sqrt A * CFC.sqrt B) * (CFC.sqrt B * CFC.sqrt A) =
          CFC.sqrt A * (CFC.sqrt B * CFC.sqrt B) * CFC.sqrt A := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_mul_self hB]
  have ht := trace_sqrt_conjTranspose_mul_eq_of_isUnit X hX
  rw [hXY, hYX] at ht
  exact congrArg Complex.re ht

/-- Joint convergence of concrete root fidelity along positive matrix
sequences in a fixed finite dimension. -/
theorem tendsto_fidelity
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {Aseq Bseq : ℕ → Matrix n n ℂ}
    (hAseq : ∀ k, (Aseq k).PosSemidef) (hBseq : ∀ k, (Bseq k).PosSemidef)
    (hAlim : Tendsto Aseq atTop (𝓝 A)) (hBlim : Tendsto Bseq atTop (𝓝 B)) :
    Tendsto (fun k => fidelity (Aseq k) (Bseq k)) atTop (𝓝 (fidelity A B)) := by
  have hin : Tendsto Bseq atTop (𝓝[{X | X.PosSemidef}] B) :=
    tendsto_nhdsWithin_iff.mpr ⟨hBlim, Filter.Eventually.of_forall hBseq⟩
  have hsqrt : Tendsto (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ)
      (𝓝[{X | X.PosSemidef}] B) (𝓝 (CFC.sqrt B)) :=
    continuousOn_matrix_sqrt B hB
  have hS : Tendsto (fun k => CFC.sqrt (Bseq k)) atTop (𝓝 (CFC.sqrt B)) :=
    hsqrt.comp hin
  have hprod : Tendsto
      (fun k => CFC.sqrt (Bseq k) * Aseq k * CFC.sqrt (Bseq k))
      atTop (𝓝 (CFC.sqrt B * A * CFC.sqrt B)) := (hS.mul hAlim).mul hS
  exact Cloning.MatrixRegularization.tendsto_trace_sqrt
    (sandwich_posSemidef hA B) hprod
    (Filter.Eventually.of_forall (fun k => sandwich_posSemidef (hAseq k) (Bseq k)))

/-- Symmetry of actual root fidelity for arbitrary positive matrices.
No invertibility or trace normalization is required. -/
theorem fidelity_symm {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : fidelity A B = fidelity B A := by
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
  have hlimAB := tendsto_fidelity hA hB (fun k => (hAseq k).posSemidef)
    (fun k => (hBseq k).posSemidef) hAlim hBlim
  have hlimBA := tendsto_fidelity hB hA (fun k => (hBseq k).posSemidef)
    (fun k => (hAseq k).posSemidef) hBlim hAlim
  have heq : (fun k => fidelity (Aseq k) (Bseq k)) =
      (fun k => fidelity (Bseq k) (Aseq k)) := by
    funext k
    exact fidelity_symm_of_isUnit (hAseq k).posSemidef (hBseq k).posSemidef
      (hAseq k).isUnit (hBseq k).isUnit
  rw [heq] at hlimAB
  exact tendsto_nhds_unique hlimAB hlimBA

end Cloning.MatrixFidelity
