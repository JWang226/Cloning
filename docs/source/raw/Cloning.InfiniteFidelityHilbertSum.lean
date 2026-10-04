import Cloning.InfiniteFidelityFiniteMixture
import Cloning.InfiniteFiniteCorner
import Cloning.MatrixFidelityBlocks
import Cloning.PCTGlobalMatrixBridge

/-! Exact fidelity additivity for positive operators in finite orthogonal
Hilbert summands. The summands need not be normalized or exhaust the ambient
space. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical
namespace Cloning.InfiniteFidelityHilbertSum
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matrixLift_basis_matrixOf {J : Type*} [Fintype J] [DecidableEq J]
    (b : OrthonormalBasis J ℂ H) (A : TraceClass H) : matrixLift b (matrixOf b A.1) = A := by
  apply Subtype.ext
  change ofMatrix b (matrixOf b A.1) = A.1
  rw [ofMatrix_matrixOf]
  have hb : projection b = 1 := by
    ext x
    rw [projection_apply]
    simpa only [OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.one_apply] using b.sum_repr x
  rw [hb, one_mul, mul_one]

theorem rootFidelity_matrixOf_basis {J : Type*} [Fintype J] [DecidableEq J]
    (b : OrthonormalBasis J ℂ H) (A B : PositiveTraceClass H) :
    MatrixFidelity.fidelity (matrixOf b A.1.1) (matrixOf b B.1.1) = A.rootFidelity B := by
  have h := fidelity_ofMatrix b.orthonormal (matrixOf_posSemidef b A.2) (matrixOf_posSemidef b B.2)
  have hA := congrArg (fun Z : TraceClass H ↦ Z.1) (matrixLift_basis_matrixOf b A.1)
  have hB := congrArg (fun Z : TraceClass H ↦ Z.1) (matrixLift_basis_matrixOf b B.1)
  change ofMatrix b (matrixOf b A.1.1) = A.1.1 at hA
  change ofMatrix b (matrixOf b B.1.1) = B.1.1 at hB
  simpa only [hA, hB, PositiveTraceClass.rootFidelity] using h.symm

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

theorem matrixLift_blockDiagonal (v : ∀ i, J i → H) (M : ∀ i, Matrix (J i) (J i) ℂ) :
    matrixLift (fun a : Sigma J ↦ v a.1 a.2) (Matrix.blockDiagonal' M) =
      ∑ i, matrixLift (v i) (M i) := by
  simp only [matrixLift, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j hj hji
    simp only [Matrix.blockDiagonal'_apply_ne M _ _ (Ne.symm hji), zero_smul, Finset.sum_const_zero]
  · simp

section Embeddings
variable {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]

theorem orthonormal_sigma_embedding (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (hV : OrthogonalFamily ℂ E V) (b : ∀ i, OrthonormalBasis (J i) ℂ (E i)) :
    Orthonormal ℂ (fun a : Sigma J ↦ V a.1 (b a.1 a.2)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,a⟩ ⟨j,c⟩
  by_cases hij : i = j
  · subst j
    rw [LinearIsometry.inner_map_map]
    simpa using orthonormal_iff_ite.mp (b i).orthonormal a c
  · have hac : (⟨i,a⟩ : Sigma J) ≠ ⟨j,c⟩ := fun h ↦ hij (congrArg Sigma.fst h)
    rw [if_neg hac]
    exact hV hij _ _

def orthogonalSum (V : ∀ i, E i →ₗᵢ[ℂ] H) (A : ∀ i, PositiveTraceClass (E i)) :
    PositiveTraceClass H := PositiveTraceClass.finsetSum Finset.univ
      (fun i ↦ (A i).map (QuantumChannel.ofIsometry (V i)).toPositiveTracePreservingMap)

theorem orthogonalSum_val (V : ∀ i, E i →ₗᵢ[ℂ] H) (A : ∀ i, PositiveTraceClass (E i)) :
    (orthogonalSum V A).1 = ∑ i, conjugationLinearMap (V i).toContinuousLinearMap (A i).1 := rfl

theorem orthogonalSum_matrixLift (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (b : ∀ i, OrthonormalBasis (J i) ℂ (E i)) (A : ∀ i, PositiveTraceClass (E i)) :
    (orthogonalSum V A).1 = matrixLift (fun a : Sigma J ↦ V a.1 (b a.1 a.2))
      (Matrix.blockDiagonal' (fun i ↦ matrixOf (b i) (A i).1.1)) := by
  rw [orthogonalSum_val, matrixLift_blockDiagonal (fun i a ↦ V i (b i a))]
  apply Finset.sum_congr rfl
  intro i hi
  have h := Cloning.PCTGlobal.conjugation_matrixLift (V i).toContinuousLinearMap (b i)
    (matrixOf (b i) (A i).1.1)
  rw [matrixLift_basis_matrixOf] at h
  exact h

/-- Exact additivity, including arbitrary positive masses, on actual finite
orthogonal isometric embeddings. No completeness of the ambient decomposition
or state-normalization premise is needed. -/
theorem rootFidelity_orthogonalSum (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (hV : OrthogonalFamily ℂ E V) (b : ∀ i, OrthonormalBasis (J i) ℂ (E i))
    (A B : ∀ i, PositiveTraceClass (E i)) :
    (orthogonalSum V A).rootFidelity (orthogonalSum V B) = ∑ i, (A i).rootFidelity (B i) := by
  have hA := congrArg (fun Z : TraceClass H ↦ Z.1) (orthogonalSum_matrixLift V b A)
  have hB := congrArg (fun Z : TraceClass H ↦ Z.1) (orthogonalSum_matrixLift V b B)
  change (orthogonalSum V A).1.1 = ofMatrix (fun a : Sigma J ↦ V a.1 (b a.1 a.2))
    (Matrix.blockDiagonal' (fun i ↦ matrixOf (b i) (A i).1.1)) at hA
  change (orthogonalSum V B).1.1 = ofMatrix (fun a : Sigma J ↦ V a.1 (b a.1 a.2))
    (Matrix.blockDiagonal' (fun i ↦ matrixOf (b i) (B i).1.1)) at hB
  change InfiniteFidelity.fidelity _ _ _ _ _ _ = _
  have h := fidelity_ofMatrix (orthonormal_sigma_embedding V hV b)
    (MatrixFidelity.blockDiagonal'_posSemidef _ (fun i ↦ matrixOf_posSemidef (b i) (A i).2))
    (MatrixFidelity.blockDiagonal'_posSemidef _ (fun i ↦ matrixOf_posSemidef (b i) (B i).2))
  simp only [← hA, ← hB] at h
  rw [h]
  rw [MatrixFidelity.fidelity_blockDiagonal' _ _
    (fun i ↦ matrixOf_posSemidef (b i) (A i).2) (fun i ↦ matrixOf_posSemidef (b i) (B i).2)]
  apply Finset.sum_congr rfl
  intro i hi
  exact rootFidelity_matrixOf_basis (b i) (A i) (B i)

end Embeddings
end Cloning.InfiniteFidelityHilbertSum
