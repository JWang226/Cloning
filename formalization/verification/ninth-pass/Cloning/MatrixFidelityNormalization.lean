import Cloning.MatrixFidelityScaling

/-!
# Canonical normalization of positive matrix blocks

The normalizing weight is the actual real trace of the block. A zero-trace
positive block is zero, so reconstruction and fidelity factorization hold
without a separate nonzero-block hypothesis or a nonempty index assumption.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A block normalized by its trace, with the zero block mapped to zero. -/
def normalizedBlock (A : Matrix n n ℂ) : Matrix n n ℂ :=
  ((Matrix.trace A).re)⁻¹ • A

omit [DecidableEq n] in
/-- Positivity forces a block with zero real trace to be identically zero. -/
theorem trace_re_eq_zero_iff {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Matrix.trace A).re = 0 ↔ A = 0 := by
  constructor
  · intro htrace
    apply hA.trace_eq_zero_iff.mp
    apply Complex.ext
    · exact htrace
    · exact trace_im_zero hA
  · rintro rfl
    simp

omit [DecidableEq n] in
theorem normalizedBlock_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (normalizedBlock A).PosSemidef :=
  hA.smul (inv_nonneg.mpr (trace_re_nonneg hA))

omit [DecidableEq n] in
theorem normalizedBlock_zero : normalizedBlock (0 : Matrix n n ℂ) = 0 := by
  simp [normalizedBlock]

omit [DecidableEq n] in
/-- Canonical normalization has real trace one whenever the original trace is positive. -/
theorem normalizedBlock_trace_re {A : Matrix n n ℂ}
    (htrace : 0 < (Matrix.trace A).re) :
    (Matrix.trace (normalizedBlock A)).re = 1 := by
  rw [normalizedBlock, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  exact inv_mul_cancel₀ htrace.ne'

omit [DecidableEq n] in
/-- The full complex trace of a normalized positive nonzero block is one. -/
theorem normalizedBlock_trace_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htrace : 0 < (Matrix.trace A).re) :
    Matrix.trace (normalizedBlock A) = 1 := by
  apply Complex.ext
  · exact normalizedBlock_trace_re htrace
  · exact trace_im_zero (normalizedBlock_posSemidef hA)

omit [DecidableEq n] in
/-- Reconstruction includes the zero-trace case, using positivity. -/
theorem normalizedBlock_reconstruct {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Matrix.trace A).re • normalizedBlock A = A := by
  by_cases ht : (Matrix.trace A).re = 0
  · have hzero := (trace_re_eq_zero_iff hA).mp ht
    rw [hzero]
    simp [normalizedBlock]
  · rw [normalizedBlock, smul_smul, mul_inv_cancel₀ ht, one_smul]

/-- Exact trace-weight factorization in the first fidelity argument. -/
theorem fidelity_normalizedBlock_left {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (B : Matrix n n ℂ) :
    fidelity A B = Real.sqrt (Matrix.trace A).re * fidelity (normalizedBlock A) B := by
  calc
    fidelity A B = fidelity ((Matrix.trace A).re • normalizedBlock A) B := by
      rw [normalizedBlock_reconstruct hA]
    _ = Real.sqrt (Matrix.trace A).re * fidelity (normalizedBlock A) B :=
      fidelity_smul_left _ _ _ (trace_re_nonneg hA) (normalizedBlock_posSemidef hA)

/-- Exact trace-weight factorization in the second fidelity argument. -/
theorem fidelity_normalizedBlock_right {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A B = Real.sqrt (Matrix.trace B).re * fidelity A (normalizedBlock B) := by
  calc
    fidelity A B = fidelity A ((Matrix.trace B).re • normalizedBlock B) := by
      rw [normalizedBlock_reconstruct hB]
    _ = Real.sqrt (Matrix.trace B).re * fidelity A (normalizedBlock B) :=
      fidelity_smul_right _ _ _ (trace_re_nonneg hB) hA (normalizedBlock_posSemidef hB)

/-- Canonical block fidelity carries the Hellinger weight of its actual traces. -/
theorem fidelity_normalizedBlocks {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A B = Real.sqrt (Matrix.trace A).re * Real.sqrt (Matrix.trace B).re *
      fidelity (normalizedBlock A) (normalizedBlock B) := by
  rw [fidelity_normalizedBlock_left hA B,
    fidelity_normalizedBlock_right (normalizedBlock_posSemidef hA) hB]
  ring

/-- The concrete maximally mixed state `I / dim`, for a nonempty finite index type. -/
def maximallyMixed (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] : State n where
  matrix := (Fintype.card n : ℝ)⁻¹ • (1 : Matrix n n ℂ)
  positive := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    apply Complex.ext
    · simp
    · simp

theorem maximallyMixed_matrix [Nonempty n] :
    (maximallyMixed n).matrix = (Fintype.card n : ℝ)⁻¹ • (1 : Matrix n n ℂ) := rfl

/-- The spectator state is precisely the canonical normalization of the identity. -/
theorem maximallyMixed_eq_normalized_one [Nonempty n] :
    (maximallyMixed n).matrix = normalizedBlock (1 : Matrix n n ℂ) := by
  simp [maximallyMixed, normalizedBlock, Matrix.trace_one]

end Cloning.MatrixFidelity
