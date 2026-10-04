import Cloning.PCTRankPurificationMatrices
import Cloning.PCTRankPurificationBlockAlgebra

/-! Actual word-matrix resolutions of the complete smaller tensor register
and its induced ambient copies. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
variable {n r d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The complete physical Schur family resolves the literal word identity. -/
theorem sum_embeddingMatrix_projection (L : List (PhysicalHighestTensor n d))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length,(L.get i).sector)=⊤) :
    (∑ i : Fin L.length,(L.get i).embeddingMatrix*(L.get i).embeddingMatrixᴴ)=1 := by
  ext w v
  have hh := (physicalSchurBasis L hL hspan).sum_inner_mul_inner
    (registerBasis (Fin n → Fin d) w) (registerBasis (Fin n → Fin d) v)
  simpa only [physicalSchurBasis_apply,physicalSchurBasisVector,PhysicalSchurBasisIndex,
    Fintype.sum_sigma,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    PhysicalHighestTensor.embeddingMatrix_apply,registerBasis_apply,register_inner_single,
    lp.inner_single_right,RCLike.inner_apply,starRingEnd_apply,mul_one,
    lp.single_apply,Pi.single_apply,Matrix.one_apply,one_mul,apply_ite,star_one,star_zero,eq_comm] using hh

/-- Orthogonality of physical cyclic copies is literal rectangular matrix
orthogonality, including different copies of the same highest weight. -/
theorem embeddingMatrix_orthogonal {ι : Type*} (H : ι → PhysicalHighestTensor n d)
    (hH : OrthogonalFamily ℂ (fun i => (H i).sector) (fun i => (H i).sector.subtypeₗᵢ))
    (i j : ι) (hij : i≠j) : (H i).embeddingMatrixᴴ*(H j).embeddingMatrix=0 := by
  ext a b
  have hh := hH hij
    ((H i).canonicalIsometry (partitionBasis (H i).weight (H i).weight_antitone a))
    ((H j).canonicalIsometry (partitionBasis (H j).weight (H j).weight_antitone b))
  change ⟪(H i).canonicalEmbedding _,(H j).canonicalEmbedding _⟫_ℂ=0 at hh
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,
    PhysicalHighestTensor.embeddingMatrix_apply,lp.inner_eq_tsum,tsum_fintype,
    RCLike.inner_apply,starRingEnd_apply,mul_comm,Matrix.zero_apply] using hh

/-- The literal rectangular inclusion of the first r physical coordinates. -/
def coordinateInclusionMatrix (r k : ℕ) : Matrix (Fin (r+k)) (Fin r) ℂ :=
  fun a b => if a=Fin.castAdd k b then 1 else 0

@[simp] theorem coordinateTensorMatrix_apply (n r k : ℕ)
    (w : Fin n → Fin (r+k)) (v : Fin n → Fin r) :
    coordinateTensorMatrix n r k w v = if (fun t => Fin.castAdd k (v t))=w then 1 else 0 := by
  simp [coordinateTensorMatrix,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply,
    coordinateTensorEmbedding,registerEmbedding_single,coordinateWordEmbedding,
    registerBasis_apply,register_inner_single,lp.single_apply,Pi.single_apply,eq_comm]

theorem coordinateTensorMatrix_eq_tensorPower (n r k : ℕ) :
    coordinateTensorMatrix n r k=tensorPower n (coordinateInclusionMatrix r k) := by
  ext w v
  rw [coordinateTensorMatrix_apply]
  simp only [tensorPower,coordinateInclusionMatrix,Fintype.prod_ite_zero,
    Finset.prod_const_one]
  congr 1
  exact propext ⟨fun h t => (congrFun h t).symm,fun h => funext (fun t => (h t).symm)⟩

/-- The rectangular inclusion itself has the exact induced-copy expansion. -/
theorem coordinateTensorMatrix_eq_sum_lift (L : List (PhysicalHighestTensor n r))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length,(L.get i).sector)=⊤) (k : ℕ) :
    coordinateTensorMatrix n r k=∑ i : Fin L.length,
      ((L.get i).liftEmbeddingMatrix k*rankSectorMatrix (L.get i).weight (L.get i).weight_antitone k)*
        (L.get i).embeddingMatrixᴴ := by
  calc
    _ = coordinateTensorMatrix n r k*(∑ i : Fin L.length,(L.get i).embeddingMatrix*(L.get i).embeddingMatrixᴴ) := by
      rw [sum_embeddingMatrix_projection L hL hspan,Matrix.mul_one]
    _ = _ := by
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Matrix.mul_assoc,← PhysicalHighestTensor.coordinateLift_embeddingMatrix]

/-- Actual coordinate support decomposed into the induced ambient copies. -/
theorem coordinateTensorMatrix_support_expansion (L : List (PhysicalHighestTensor n r))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length,(L.get i).sector)=⊤) (k : ℕ) :
    coordinateTensorMatrix n r k*(coordinateTensorMatrix n r k)ᴴ=
      ∑ i : Fin L.length,
        (L.get i).liftEmbeddingMatrix k *
          (rankSectorMatrix (L.get i).weight (L.get i).weight_antitone k *
            (rankSectorMatrix (L.get i).weight (L.get i).weight_antitone k)ᴴ) *
          ((L.get i).liftEmbeddingMatrix k)ᴴ := by
  rw [Cloning.PCTRankPurification.conjugated_identity_resolution
    (fun i : Fin L.length => (L.get i).embeddingMatrix)
    (sum_embeddingMatrix_projection L hL hspan)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← PhysicalHighestTensor.coordinateLift_embeddingMatrix]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

end Cloning.TensorLie
