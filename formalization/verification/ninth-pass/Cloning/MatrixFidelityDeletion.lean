import Cloning.MatrixFidelityLifted
import Cloning.MatrixFidelityProjector
import Cloning.MatrixSqrtSubadditivity
import Cloning.MatrixFidelityTraceBound

/-!
# Removing positive matrix blocks

The dimension-independent deletion bound is derived from concrete matrix
square-root subadditivity, fidelity monotonicity, and the trace-product
bound. The final theorem supplies the retained-block quantum estimate used
in the manuscript, without an assumed fidelity-continuity inequality.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Root fidelity is subadditive in a positive matrix argument. -/
theorem fidelity_add_le {G B : Matrix n n ℂ} (hG : G.PosSemidef)
    (hB : B.PosSemidef) (T : Matrix n n ℂ) :
    fidelity (G + B) T ≤ fidelity G T + fidelity B T := by
  unfold fidelity
  rw [Matrix.mul_add, Matrix.add_mul]
  exact trace_sqrt_add_le (sandwich_posSemidef hG T) (sandwich_posSemidef hB T)

/-- Removing a positive summand changes root fidelity by at most the
square root of the product of its mass and the target mass. -/
theorem fidelity_deletion_bound {G B T : Matrix n n ℂ}
    (hG : G.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef) :
    |fidelity (G + B) T - fidelity G T| ≤
      Real.sqrt ((Matrix.trace B).re * (Matrix.trace T).re) := by
  have horder : G ≤ G + B := by
    change ((G + B) - G).PosSemidef
    simpa using hB
  have hmono := fidelity_mono_left horder T
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  calc
    fidelity (G + B) T - fidelity G T ≤ fidelity B T := by
      linarith [fidelity_add_le hG hB T]
    _ ≤ Real.sqrt ((Matrix.trace B).re * (Matrix.trace T).re) :=
      fidelity_le_sqrt_trace_mul_trace hB hT

/-- For a subnormalized target, only the removed mass enters the estimate. -/
theorem fidelity_deletion_bound_trace_le_one {G B T : Matrix n n ℂ}
    (hG : G.PosSemidef) (hB : B.PosSemidef) (hT : T.PosSemidef)
    (htrace : (Matrix.trace T).re ≤ 1) :
    |fidelity (G + B) T - fidelity G T| ≤ Real.sqrt (Matrix.trace B).re := by
  apply (fidelity_deletion_bound hG hB hT).trans
  apply Real.sqrt_le_sqrt
  simpa using mul_le_mul_of_nonneg_left htrace (trace_re_nonneg hB)

/-- Deletion stated as positive domination of the retained matrix. -/
theorem fidelity_retained_bound {X G T : Matrix n n ℂ}
    (hG : G.PosSemidef) (hdiff : (X - G).PosSemidef) (hT : T.PosSemidef)
    (htrace : (Matrix.trace T).re ≤ 1) :
    |fidelity X T - fidelity G T| ≤
      Real.sqrt ((Matrix.trace X).re - (Matrix.trace G).re) := by
  have h := fidelity_deletion_bound_trace_le_one hG hdiff hT htrace
  have hsum : G + (X - G) = X := by rw [add_comm G, sub_add_cancel]
  simpa only [hsum, Matrix.trace_sub, Complex.sub_re] using h

section Lifted

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d s : ι → Type*}
variable [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
variable [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]

/-- The exact lifted deletion estimate before canonical sector normalization. -/
theorem lifted_deletion_raw_bound
    (X G ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p : ι → ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hG : ∀ i, (G i).PosSemidef)
    (hρ : ∀ i, (ρ i).PosSemidef) (hτ : ∀ i, (τ i).PosSemidef)
    (hp : ∀ i, 0 ≤ p i) (hdiff : ∀ i, (X i - G i).PosSemidef)
    (hρtrace : ∀ i, (Matrix.trace (ρ i)).re = 1)
    (hτtrace : ∀ i, (Matrix.trace (τ i)).re = 1)
    (hpsum : ∑ i, p i = 1) :
    |fidelity (Matrix.blockDiagonal' (fun i ↦ X i ⊗ₖ τ i))
        (Matrix.blockDiagonal' (fun i ↦ (p i • ρ i) ⊗ₖ τ i)) -
      fidelity (Matrix.blockDiagonal' (fun i ↦ G i ⊗ₖ τ i))
        (Matrix.blockDiagonal' (fun i ↦ (p i • ρ i) ⊗ₖ τ i))| ≤
      Real.sqrt (∑ i, ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re)) := by
  have hmass i : 0 ≤ (Matrix.trace (X i)).re - (Matrix.trace (G i)).re := by
    simpa only [Matrix.trace_sub, Complex.sub_re] using trace_re_nonneg (hdiff i)
  have hlocal i : |fidelity (X i) (ρ i) - fidelity (G i) (ρ i)| ≤
      Real.sqrt ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re) :=
    fidelity_retained_bound (hG i) (hdiff i) (hρ i) (hρtrace i).le
  rw [fidelity_lifted_blocks X ρ τ p hX hρ hτ hp hτtrace,
    fidelity_lifted_blocks G ρ τ p hG hρ hτ hp hτtrace,
    ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    |∑ i, Real.sqrt (p i) * (fidelity (X i) (ρ i) - fidelity (G i) (ρ i))| ≤
        ∑ i, |Real.sqrt (p i) * (fidelity (X i) (ρ i) - fidelity (G i) (ρ i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, Real.sqrt (p i) *
        Real.sqrt ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hlocal i) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (∑ i, p i) *
        Real.sqrt (∑ i, ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re)) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ hp hmass
    _ = Real.sqrt (∑ i, ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re)) := by
      rw [hpsum, Real.sqrt_one, one_mul]

/-- The manuscript's retained-block quantum estimate with canonical block
weights and sector states. Every fidelity here is the concrete matrix root
fidelity; no quantum-continuity assumption remains in the statement. -/
theorem lifted_deletion_bound
    (X G ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p : ι → ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hG : ∀ i, (G i).PosSemidef)
    (hρ : ∀ i, (ρ i).PosSemidef) (hτ : ∀ i, (τ i).PosSemidef)
    (hp : ∀ i, 0 ≤ p i) (hdiff : ∀ i, (X i - G i).PosSemidef)
    (hρtrace : ∀ i, (Matrix.trace (ρ i)).re = 1)
    (hτtrace : ∀ i, (Matrix.trace (τ i)).re = 1)
    (hpsum : ∑ i, p i = 1) :
    |fidelity (Matrix.blockDiagonal' (fun i ↦ X i ⊗ₖ τ i))
        (Matrix.blockDiagonal' (fun i ↦ (p i • ρ i) ⊗ₖ τ i)) -
      ∑ i, Real.sqrt (Matrix.trace (G i)).re * Real.sqrt (p i) *
        fidelity (normalizedBlock (G i)) (ρ i)| ≤
      Real.sqrt (∑ i, ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re)) := by
  rw [← fidelity_lifted_blocks_normalized G ρ τ p hG hρ hτ hp hτtrace]
  exact lifted_deletion_raw_bound X G ρ τ p hX hG hρ hτ hp hdiff hρtrace hτtrace hpsum

end Lifted

end Cloning.MatrixFidelity
