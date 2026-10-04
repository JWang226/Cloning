import Cloning.InfiniteFidelity
import Cloning.InfinitePureStateContinuity
import Cloning.InfiniteHilbertSchmidtPositive
import Cloning.InfiniteTraceClassCutoffConvergence

/-!
# Concrete finite matrix corners of an arbitrary Hilbert space

A finite orthonormal family identifies matrices with finite-rank operators.
This file constructs that identification using actual rank-one operators and
proves its multiplication, adjoint, trace, positive-square-root, and fidelity
identities. No trace or functional-calculus compatibility is assumed.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder InnerProductSpace Topology BigOperators Matrix
open Filter

namespace Cloning.InfiniteFiniteCorner

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open InfiniteTraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The analytic trace of a general rank-one operator. -/
theorem traceCLM_rankOneOperator (x y : H) :
    traceCLM (rankOneOperator x y) = ⟪y, x⟫_ℂ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  change trace (InnerProductSpace.rankOne ℂ x y) _ = _
  rw [trace_eq_of_hilbertBasis _ b]
  simpa only [InnerProductSpace.rankOne_apply, inner_smul_right, mul_comm] using
    (b.hasSum_inner_mul_inner y x).tsum_eq

/-- A finite matrix, bundled with its actual trace-class realization. -/
def matrixLift (v : ι → H) (M : Matrix ι ι ℂ) : TraceClass H :=
  ∑ i, ∑ j, M i j • rankOneOperator (v i) (v j)

/-- The corresponding bounded operator on the ambient Hilbert space. -/
def ofMatrix (v : ι → H) (M : Matrix ι ι ℂ) : H →L[ℂ] H := (matrixLift v M).1

theorem ofMatrix_traceClass (v : ι → H) (M : Matrix ι ι ℂ) :
    IsTraceClass (ofMatrix v M) := (matrixLift v M).2

theorem ofMatrix_eq_sum (v : ι → H) (M : Matrix ι ι ℂ) :
    ofMatrix v M = ∑ i, ∑ j, M i j • InnerProductSpace.rankOne ℂ (v i) (v j) := by
  change inclusionCLM (matrixLift v M) = _
  simp only [matrixLift, map_sum, map_smul, inclusionCLM_apply,
    rankOneOperator, TraceClass.ofOperator_coe]

theorem ofMatrix_apply (v : ι → H) (M : Matrix ι ι ℂ) (z : H) :
    ofMatrix v M z = ∑ i, (∑ j, M i j * ⟪v j, z⟫_ℂ) • v i := by
  simp only [ofMatrix_eq_sum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
    smul_smul, Finset.sum_smul]

theorem inner_ofMatrix_apply {v : ι → H} (hv : Orthonormal ℂ v)
    (M : Matrix ι ι ℂ) (z : H) (i : ι) :
    ⟪v i, ofMatrix v M z⟫_ℂ = ∑ j, M i j * ⟪v j, z⟫_ℂ := by
  rw [ofMatrix_apply]
  exact hv.inner_right_fintype _ _

theorem ofMatrix_mul {v : ι → H} (hv : Orthonormal ℂ v) (M N : Matrix ι ι ℂ) :
    ofMatrix v (M * N) = ofMatrix v M * ofMatrix v N := by
  ext z
  rw [ContinuousLinearMap.mul_apply, ofMatrix_apply v M, ofMatrix_apply v (M * N)]
  simp_rw [inner_ofMatrix_apply hv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem ofMatrix_conjTranspose (v : ι → H) (M : Matrix ι ι ℂ) :
    ofMatrix v M.conjTranspose = star (ofMatrix v M) := by
  simp only [ofMatrix_eq_sum, star_sum, star_smul, Matrix.conjTranspose_apply,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
  exact Finset.sum_comm

theorem ofMatrix_nonneg {v : ι → H} (hv : Orthonormal ℂ v)
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : 0 ≤ ofMatrix v M := by
  rw [← MatrixFidelity.sqrt_mul_self hM, ofMatrix_mul hv]
  have hstar : star (ofMatrix v (CFC.sqrt M)) = ofMatrix v (CFC.sqrt M) := by
    rw [← ofMatrix_conjTranspose, MatrixFidelity.sqrt_conjTranspose]
  simpa only [hstar] using star_mul_self_nonneg (ofMatrix v (CFC.sqrt M))

theorem sqrt_ofMatrix {v : ι → H} (hv : Orthonormal ℂ v)
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    CFC.sqrt (ofMatrix v M) = ofMatrix v (CFC.sqrt M) := by
  apply CFC.sqrt_unique
  · rw [← ofMatrix_mul hv, MatrixFidelity.sqrt_mul_self hM]
  · exact ofMatrix_nonneg hv (MatrixFidelity.sqrt_posSemidef M)

theorem trace_ofMatrix {v : ι → H} (hv : Orthonormal ℂ v) (M : Matrix ι ι ℂ) :
    trace (ofMatrix v M) (ofMatrix_traceClass v M) = Matrix.trace M := by
  change traceCLM (matrixLift v M) = _
  simp only [matrixLift, map_sum, map_smul, traceCLM_rankOneOperator,
    orthonormal_iff_ite.mp hv, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.trace, Matrix.diag]
  simp

/-- Analytic infinite-dimensional fidelity agrees exactly with finite matrix
fidelity on a finite orthonormal corner. -/
theorem fidelity_ofMatrix {v : ι → H} (hv : Orthonormal ℂ v)
    {M N : Matrix ι ι ℂ} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    InfiniteFidelity.fidelity (ofMatrix v M) (ofMatrix v N)
      (ofMatrix_nonneg hv hM) (ofMatrix_nonneg hv hN)
      (ofMatrix_traceClass v M) (ofMatrix_traceClass v N) = MatrixFidelity.fidelity M N := by
  rw [InfiniteFidelity.fidelity_eq_trace_sqrt_sandwich]
  have heq : CFC.sqrt (CFC.sqrt (ofMatrix v N) * ofMatrix v M * CFC.sqrt (ofMatrix v N)) =
      ofMatrix v (CFC.sqrt (CFC.sqrt N * M * CFC.sqrt N)) := by
    rw [sqrt_ofMatrix hv hN, ← ofMatrix_mul hv, ← ofMatrix_mul hv,
      sqrt_ofMatrix hv (MatrixFidelity.sandwich_posSemidef hM N)]
  have htrace {X Y : H →L[ℂ] H} (he : X = Y) (hX : IsTraceClass X) (hY : IsTraceClass Y) :
      trace X hX = trace Y hY := by subst Y; rfl
  exact congrArg Complex.re ((htrace heq _ _).trans (trace_ofMatrix hv _))

/-- The actual matrix coefficients of an ambient operator. -/
def matrixOf (v : ι → H) (A : H →L[ℂ] H) : Matrix ι ι ℂ :=
  fun i j => ⟪v i, A (v j)⟫_ℂ

/-- The orthogonal projection when `v` is orthonormal. -/
def projection (v : ι → H) : H →L[ℂ] H := ofMatrix v 1

theorem projection_eq_sum (v : ι → H) :
    projection v = ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i) := by
  simp [projection, ofMatrix_eq_sum, Matrix.one_apply]

theorem projection_apply (v : ι → H) (x : H) :
    projection v x = ∑ i, ⟪v i, x⟫_ℂ • v i := by
  simp only [projection_eq_sum, ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply]

theorem matrixOf_posSemidef (v : ι → H) {A : H →L[ℂ] H} (hA : 0 ≤ A) :
    (matrixOf v A).PosSemidef := matrixCoefficients_posSemidef hA v

/-- Reconstructing the coefficients gives the actual two-sided compression. -/
theorem ofMatrix_matrixOf (v : ι → H) (A : H →L[ℂ] H) :
    ofMatrix v (matrixOf v A) = projection v * A * projection v := by
  ext x
  simp only [ofMatrix_apply, matrixOf, ContinuousLinearMap.mul_apply, projection_apply,
    map_sum, map_smul, Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm]
  exact Finset.sum_comm

theorem matrixOf_ofMatrix {v : ι → H} (hv : Orthonormal ℂ v) (M : Matrix ι ι ℂ) :
    matrixOf v (ofMatrix v M) = M := by
  ext i j
  simp [matrixOf, inner_ofMatrix_apply hv, orthonormal_iff_ite.mp hv]

/-- Every finite subset of a Hilbert basis is an actual orthonormal corner. -/
theorem basisFamily_orthonormal {κ : Type*} (b : HilbertBasis κ ℂ H) (s : Finset κ) :
    Orthonormal ℂ (fun i : s => b i) := b.orthonormal.comp Subtype.val Subtype.val_injective

theorem projection_basis {κ : Type*} [DecidableEq κ] (b : HilbertBasis κ ℂ H) (s : Finset κ) :
    projection (fun i : s => b i) = basisProjection b s := by
  classical
  rw [projection_eq_sum, basisProjection]
  exact Finset.sum_coe_sort s (fun i => InnerProductSpace.rankOne ℂ (b i) (b i))

/-- Coefficients in a finite Hilbert-basis set reconstruct precisely the basis
projection compression; this includes the empty corner. -/
theorem ofMatrix_matrixOf_basis {κ : Type*} [DecidableEq κ] (b : HilbertBasis κ ℂ H) (s : Finset κ)
    (A : H →L[ℂ] H) :
    ofMatrix (fun i : s => b i) (matrixOf (fun i : s => b i) A) =
      basisProjection b s * A * basisProjection b s := by
  classical
  rw [ofMatrix_matrixOf, projection_basis]

end Cloning.InfiniteFiniteCorner
