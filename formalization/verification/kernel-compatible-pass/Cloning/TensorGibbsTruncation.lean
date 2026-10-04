import Cloning.InfiniteFiniteCorner
import Cloning.TensorLANEmbeddingAction

/-! Positive spectral truncation in an actual finite orthonormal frame. The
trace-norm error is exactly the discarded trace, without a square-root loss. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.InfiniteTraceClass
open Cloning.InfiniteFiniteCorner
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projection_isStarProjection {v : ι → H} (hv : Orthonormal ℂ v) :
    IsStarProjection (projection v) := by
  constructor
  · change ofMatrix v 1 * ofMatrix v 1 = ofMatrix v 1
    rw [← ofMatrix_mul hv, one_mul]
  · change star (ofMatrix v 1) = ofMatrix v 1
    rw [← ofMatrix_conjTranspose, Matrix.conjTranspose_one]

theorem mul_projection_eq_eigenmatrix (A : H →L[ℂ] H) (v : ι → H) (lam : ι → ℝ)
    (hev : ∀ i, A (v i) = (lam i : ℂ) • v i) :
    A * projection v = ofMatrix v (Matrix.diagonal (fun i => (lam i : ℂ))) := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, projection_apply, map_sum, map_smul, hev,
    ofMatrix_apply, Matrix.diagonal_apply, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem spectralFrame_residual_nonneg (A : TraceClass H) (hA : 0 ≤ A.1)
    (v : ι → H) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    (hev : ∀ i, A.1 (v i) = (lam i : ℂ) • v i) :
    0 ≤ (A - frameMatrix v (Matrix.diagonal (fun i => (lam i : ℂ)))).1 := by
  let P := projection v
  let B := ofMatrix v (Matrix.diagonal (fun i => (lam i : ℂ)))
  have hP : IsStarProjection P := projection_isStarProjection hv
  have hB : IsSelfAdjoint B := by
    change star (ofMatrix v _) = ofMatrix v _
    rw [← ofMatrix_conjTranspose]
    congr 1
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply, h, Ne.symm h]
  have hAP : A.1 * P = B := mul_projection_eq_eigenmatrix A.1 v lam hev
  have hPA : P * A.1 = B := by
    have hs := congrArg star hAP
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg hA).star_eq,
      hB.star_eq] using hs
  have hPAP : P * A.1 * P = B := by
    rw [mul_assoc, hAP]
    change ofMatrix v 1 * ofMatrix v _ = _
    rw [← ofMatrix_mul hv, one_mul]
  have he : A.1 - B = (1-P) * A.1 * (1-P) := by
    calc
      _ = A.1 - A.1 * P - P * A.1 + P * A.1 * P := by rw [hPAP,hAP,hPA]; abel
      _ = _ := by noncomm_ring
  change 0 ≤ A.1 - B
  rw [he]
  exact hP.one_sub.isSelfAdjoint.conjugate_nonneg hA

theorem spectralFrame_residual_norm (A : TraceClass H) (hA : 0 ≤ A.1)
    (v : ι → H) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    (hev : ∀ i, A.1 (v i) = (lam i : ℂ) • v i) :
    ‖A - frameMatrix v (Matrix.diagonal (fun i => (lam i : ℂ)))‖ =
      (traceCLM A).re - ∑ i, lam i := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (spectralFrame_residual_nonneg A hA v hv lam hev)]
  change (traceCLM (A - frameMatrix v (Matrix.diagonal (fun i => (lam i : ℂ))))).re = _
  rw [map_sub, Complex.sub_re]
  congr 1
  have hh := trace_ofMatrix hv (Matrix.diagonal (fun i => (lam i : ℂ)))
  change traceCLM (frameMatrix v (Matrix.diagonal (fun i => (lam i : ℂ)))) = _ at hh
  rw [hh]
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]


theorem frameMatrix_diagonal (v : ι → H) (a : ι → ℝ) :
    frameMatrix v (Matrix.diagonal (fun i => (a i : ℂ))) =
      ∑ i, (a i : ℂ) • vectorProjector (v i) := by
  simp [frameMatrix, Matrix.diagonal_apply, vectorProjector, rankOneOperator]

theorem frameMatrix_diagonal_nonneg (v : ι → H) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ (frameMatrix v (Matrix.diagonal (fun i => (a i : ℂ)))).1 := by
  rw [frameMatrix_diagonal]
  change 0 ≤ inclusionCLM (∑ i, (a i : ℂ) • vectorProjector (v i))
  simp only [map_sum, map_smul]
  apply Finset.sum_nonneg
  intro i _
  change 0 ≤ (a i : ℂ) • InnerProductSpace.rankOne ℂ (v i) (v i)
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (InnerProductSpace.isPositive_rankOne_self (v i)).smul_of_nonneg
  exact_mod_cast ha i

theorem frameMatrix_diagonal_sub_norm_le (v : ι → H) (hv : ∀ i, ‖v i‖ = 1)
    (a b : ι → ℝ) :
    ‖frameMatrix v (Matrix.diagonal (fun i => (a i : ℂ))) -
      frameMatrix v (Matrix.diagonal (fun i => (b i : ℂ)))‖ ≤ ∑ i, |a i - b i| := by
  rw [frameMatrix_diagonal, frameMatrix_diagonal, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(a i : ℂ) • vectorProjector (v i) - (b i : ℂ) • vectorProjector (v i)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_smul, ← Complex.ofReal_sub, norm_weighted_projector _ (hv i)]

end Cloning.InfiniteTraceClass
