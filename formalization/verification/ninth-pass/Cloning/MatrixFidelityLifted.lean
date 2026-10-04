import Cloning.MatrixFidelityBlocks
import Cloning.MatrixFidelityTensor
import Cloning.MatrixFidelityScaling
import Cloning.MatrixFidelityNormalization

/-!
# Exact fidelity of lifted finite matrix blocks

This is the concrete matrix identity used in Proposition
`lifted-kernel-bound` of `cloning.tex`. All orthogonal-sum, tensor-product, and
scaling laws are derived in the imported files from the actual positive matrix
square root. Representation-theoretic identification of the physical Schur
blocks is not part of this matrix theorem.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d s : ι → Type*}
variable [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
variable [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]

/-- Exact lifted-block fidelity, including normalized auxiliary factors of
independently varying dimensions. The blocks `X i` may be unnormalized. -/
theorem fidelity_lifted_blocks
    (X ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p : ι → ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hρ : ∀ i, (ρ i).PosSemidef)
    (hτ : ∀ i, (τ i).PosSemidef) (hp : ∀ i, 0 ≤ p i)
    (htrace : ∀ i, (Matrix.trace (τ i)).re = 1) :
    fidelity (Matrix.blockDiagonal' (fun i => X i ⊗ₖ τ i))
      (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) =
      ∑ i, Real.sqrt (p i) * fidelity (X i) (ρ i) := by
  rw [fidelity_blockDiagonal' _ _ (fun i => (hX i).kronecker (hτ i))
    (fun i => ((hρ i).smul (hp i)).kronecker (hτ i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [fidelity_common_ancilla (hX i) ((hρ i).smul (hp i)) (hτ i) (htrace i),
    fidelity_smul_right (p i) (X i) (ρ i) (hp i) (hX i) (hρ i)]

/-- When both families have explicit classical weights, each normalized sector
fidelity is multiplied by the corresponding Hellinger weight. -/
theorem fidelity_weighted_lifted_blocks
    (σ ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p q : ι → ℝ)
    (hσ : ∀ i, (σ i).PosSemidef) (hρ : ∀ i, (ρ i).PosSemidef)
    (hτ : ∀ i, (τ i).PosSemidef) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (htrace : ∀ i, (Matrix.trace (τ i)).re = 1) :
    fidelity (Matrix.blockDiagonal' (fun i => (q i • σ i) ⊗ₖ τ i))
      (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) =
      ∑ i, Real.sqrt (q i) * Real.sqrt (p i) * fidelity (σ i) (ρ i) := by
  rw [fidelity_lifted_blocks _ ρ τ p (fun i => (hσ i).smul (hq i)) hρ hτ hp htrace]
  apply Finset.sum_congr rfl
  intro i _
  rw [fidelity_smul_left (q i) (σ i) (ρ i) (hq i) (hσ i)]
  ring

/-- The retained-block step of the paper's factorization argument, with actual
matrix fidelity throughout. Zero-weight sectors require no approximation. -/
theorem fidelity_weighted_lifted_blocks_error
    (σ ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p q : ι → ℝ) (c η : ℝ)
    (hσ : ∀ i, (σ i).PosSemidef) (hρ : ∀ i, (ρ i).PosSemidef)
    (hτ : ∀ i, (τ i).PosSemidef) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (htrace : ∀ i, (Matrix.trace (τ i)).re = 1)
    (hps : ∑ i, p i ≤ 1) (hqs : ∑ i, q i ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ i, 0 < q i → |fidelity (σ i) (ρ i) - c| ≤ η) :
    |fidelity (Matrix.blockDiagonal' (fun i => (q i • σ i) ⊗ₖ τ i))
      (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) -
      c * Cloning.BlockFidelity.classicalAffinity q p| ≤ η := by
  rw [fidelity_weighted_lifted_blocks σ ρ τ p q hσ hρ hτ hp hq htrace]
  exact Cloning.BlockFidelity.weighted_sector_error p q
    (fun i => fidelity (σ i) (ρ i)) c η hp hq hps hqs hη hsector

/-- Canonical trace-weight factorization: the output-label weights are the
actual traces of the blocks, including zero blocks. No separate choice of
output weights or normalized sector states is required. -/
theorem fidelity_lifted_blocks_normalized
    (X ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p : ι → ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hρ : ∀ i, (ρ i).PosSemidef)
    (hτ : ∀ i, (τ i).PosSemidef) (hp : ∀ i, 0 ≤ p i)
    (htrace : ∀ i, (Matrix.trace (τ i)).re = 1) :
    fidelity (Matrix.blockDiagonal' (fun i => X i ⊗ₖ τ i))
      (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) =
      ∑ i, Real.sqrt (Matrix.trace (X i)).re * Real.sqrt (p i) *
        fidelity (normalizedBlock (X i)) (ρ i) := by
  rw [fidelity_lifted_blocks X ρ τ p hX hρ hτ hp htrace]
  apply Finset.sum_congr rfl
  intro i _
  rw [fidelity_normalizedBlock_left (hX i) (ρ i)]
  ring

/-- The retained-block estimate with the output marginal extracted directly
from the concrete positive blocks. Only positive-trace sectors need satisfy the
uniform sector estimate. -/
theorem fidelity_lifted_blocks_normalized_error
    (X ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p : ι → ℝ) (c η : ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hρ : ∀ i, (ρ i).PosSemidef)
    (hτ : ∀ i, (τ i).PosSemidef) (hp : ∀ i, 0 ≤ p i)
    (htrace : ∀ i, (Matrix.trace (τ i)).re = 1)
    (hps : ∑ i, p i ≤ 1) (hXs : ∑ i, (Matrix.trace (X i)).re ≤ 1)
    (hη : 0 ≤ η)
    (hsector : ∀ i, 0 < (Matrix.trace (X i)).re →
      |fidelity (normalizedBlock (X i)) (ρ i) - c| ≤ η) :
    |fidelity (Matrix.blockDiagonal' (fun i => X i ⊗ₖ τ i))
      (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) -
      c * Cloning.BlockFidelity.classicalAffinity
        (fun i => (Matrix.trace (X i)).re) p| ≤ η := by
  rw [fidelity_lifted_blocks_normalized X ρ τ p hX hρ hτ hp htrace]
  exact Cloning.BlockFidelity.weighted_sector_error p
    (fun i => (Matrix.trace (X i)).re)
    (fun i => fidelity (normalizedBlock (X i)) (ρ i)) c η hp
    (fun i => trace_re_nonneg (hX i)) hps hXs hη hsector

end Cloning.MatrixFidelity
