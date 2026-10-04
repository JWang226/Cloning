import Cloning.PhysicalFlatPinchingMoments
import Cloning.TensorFlatProjectorMatrix

/-! Literal rank-flat output blocks in the actual canonical sector basis.
Zero-rank unsupported projectors are retained throughout the identities. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.InfiniteFiniteCorner Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem partitionActionMatrix_smul {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ)
    (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    partitionActionMatrix μ hμ (c • X) = c^(∑ a,μ a) • partitionActionMatrix μ hμ X := by
  have he : partitionTensorAction μ hμ (c • X) = c^(∑ a,μ a) • partitionTensorAction μ hμ X := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun T : TensorRegister (∑ a,μ a) (Fin d) →L[ℂ] TensorRegister (∑ a,μ a) (Fin d) =>
      T (x : TensorRegister (∑ a,μ a) (Fin d))) (tensorOperator_smul c X)
  ext i j
  simp only [partitionActionMatrix_apply, he, ContinuousLinearMap.smul_apply, inner_smul_right,
    Matrix.smul_apply, smul_eq_mul]

theorem partitionActionMatrix_rankFlat_projection {r k : ℕ} (μ : Fin (r+k) → ℕ) (hμ : Antitone μ) :
    partitionActionMatrix μ hμ (Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ))) =
      ((1/(r:ℝ))^(∑ a,μ a)) • partitionCoordinateProjection μ hμ := by
  have hm : Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ)) =
      ((1/(r:ℝ) : ℝ) : ℂ) • coordinateSupportMatrix r k := by
    rw [coordinateSupportMatrix, ← Matrix.diagonal_smul]
    congr 1
    funext a
    simp only [rankFlatSpectrum, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hm, partitionActionMatrix_smul]
  ext i j
  simp only [partitionCoordinateProjection, Matrix.smul_apply, Complex.real_smul,
    smul_eq_mul, Complex.ofReal_pow]

theorem canonicalTensorWeight_matrix {n d : ℕ} (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    matrixOf (partitionBasis H.weight H.weight_antitone) (canonicalTensorWeight H X).1 =
      partitionActionMatrix H.weight H.weight_antitone X := by
  ext i j
  rw [partitionActionMatrix_apply]
  rfl

/-- The actual target block is the conjugate of the literal coordinate
support projector, with coefficient r^(-n), also on unsupported copies. -/
theorem canonicalTensorWeight_rotated_rankFlat_matrix {n r k : ℕ}
    (H : PhysicalHighestTensor n (r+k)) (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) :
    matrixOf (partitionBasis H.weight H.weight_antitone)
      (canonicalTensorWeight H (U * Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ)) * Uᴴ)).1 =
      partitionActionMatrix H.weight H.weight_antitone U *
        (((1/(r:ℝ))^n) • partitionCoordinateProjection H.weight H.weight_antitone) *
          (partitionActionMatrix H.weight H.weight_antitone U)ᴴ := by
  rw [canonicalTensorWeight_matrix, partitionActionMatrix_mul, partitionActionMatrix_mul,
    partitionActionMatrix_star, partitionActionMatrix_rankFlat_projection, H.weight_sum]

theorem character_rankFlat_eq_projection_trace {n r k : ℕ} (H : PhysicalHighestTensor n (r+k)) :
    H.character (rankFlatSpectrum r k) = (1/(r:ℝ))^n *
      (Matrix.trace (partitionCoordinateProjection H.weight H.weight_antitone)).re := by
  have he : H.character (rankFlatSpectrum r k) =
      (Matrix.trace (partitionActionMatrix H.weight H.weight_antitone
        (Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ))))).re := by
    rw [H.character_eq_trace _ (rankFlatSpectrum_nonneg r k), partitionActionMatrix,
      ← LinearMap.trace_eq_matrix_trace]
    rfl
  rw [he, partitionActionMatrix_rankFlat_projection, H.weight_sum, Matrix.trace_smul]
  simp only [Complex.real_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The literal projector-trace output factor is the inverse physical
dimension-ratio moment. No positive-rank premise is required per copy. -/
theorem flat_projection_output_inverse_moment (n r k : ℕ) (hr : 0 < r) :
    (∑ i : SchurCopy n (r+k),
      (1/(r:ℝ))^n * (Matrix.trace (partitionCoordinateProjection
        ((recursivePhysicalDecomposition n (r+k)).get i).weight
        ((recursivePhysicalDecomposition n (r+k)).get i).weight_antitone)).re^2 /
      (partitionDimension ((recursivePhysicalDecomposition n (r+k)).get i).weight
        ((recursivePhysicalDecomposition n (r+k)).get i).weight_antitone : ℝ)) =
    ∑ μ : Shape r n, (tensorFlatYoungPMF n r hr μ).toReal *
      (dimensionRatio r k (fun a => ((μ a).val : ℝ)))⁻¹ := by
  rw [← flat_output_inverse_moment n r k hr]
  apply Finset.sum_congr rfl
  intro i _
  rw [character_rankFlat_eq_projection_trace]
  have hc : (1/(r:ℝ))^n ≠ 0 := pow_ne_zero _ (one_div_ne_zero (Nat.cast_ne_zero.mpr hr.ne'))
  field_simp
  <;> ring

end Cloning.PhysicalFlatConverse
