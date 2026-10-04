import Cloning.PCTRankPurificationBlockMatrices
import Cloning.PCTRankPurificationCoefficients

/-! The literal rectangular Haar marginal has the exact induced physical
Schur blocks. Its normalizer acts by the proved dimension ratio. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.TensorLie Cloning.PCTPurificationChannel Cloning.PhysicalFlatConverse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
variable {n r : ℕ} [NeZero r]
local instance (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

private theorem sandwich_intertwines {A B : Type*} [Fintype A] [Fintype B]
    (T : Matrix A A ℂ) (E : Matrix A B ℂ) (V M : Matrix B B ℂ) (h : T*E=E*V) :
    T*(E*M*Eᴴ)*Tᴴ=E*(V*M*Vᴴ)*Eᴴ := by
  calc
    _ = (T*E)*M*(T*E)ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [h]; simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- The actual input marginal of the rectangular purification Haar moment. -/
def coordinateHaarMarginal (n r k : ℕ) [NeZero r] :
    Matrix (Fin n → Fin (r+k)) (Fin n → Fin (r+k)) ℂ :=
  Cloning.Compression.partialTrace (rectangularHaarMoment n (coordinateInclusionMatrix r k))

theorem coordinateHaarMarginal_posSemidef (n r k : ℕ) [NeZero r] :
    (coordinateHaarMarginal n r k).PosSemidef :=
  partialTrace_rectangularHaarMoment_posSemidef n _

variable (L : List (PhysicalHighestTensor n r))
  (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
    (fun i => (L.get i).sector.subtypeₗᵢ))
  (hspan : (⨆ i : Fin L.length,(L.get i).sector)=⊤)
include hL hspan

/-- Exact block expansion of the actual Haar integral, with every physical
multiplicity copy retained separately. -/
theorem coordinateHaarMarginal_eq_blocks (k : ℕ) :
    coordinateHaarMarginal n r k =
      ∑ i : Fin L.length,
        ((partitionDimension (L.get i).weight (L.get i).weight_antitone : ℂ)/
          (partitionDimension (padPartition (L.get i).weight k)
            (padPartition_antitone _ (L.get i).weight_antitone k) : ℂ)) •
        ((L.get i).liftEmbeddingMatrix k*((L.get i).liftEmbeddingMatrix k)ᴴ) := by
  let E (i : Fin L.length) := (L.get i).liftEmbeddingMatrix k
  let Q (i : Fin L.length) := rankSectorMatrix (L.get i).weight (L.get i).weight_antitone k
  let V (i : Fin L.length) (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :=
    partitionActionMatrix (padPartition (L.get i).weight k)
      (padPartition_antitone _ (L.get i).weight_antitone k) U
  have hint (i : Fin L.length) : Integrable (fun U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ) =>
      E i*(V i U*(Q i*(Q i)ᴴ)*(V i U)ᴴ)*(E i)ᴴ) unitaryHaar :=
    (rectangularSandwichCLM (E i)).integrable_comp (integrable_partitionSandwich _ _ (Q i*(Q i)ᴴ))
  have he (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
      tensorPower n (U.val*(coordinateInclusionMatrix r k*(coordinateInclusionMatrix r k)ᴴ)*U.valᴴ)=
      ∑ i : Fin L.length,E i*(V i U*(Q i*(Q i)ᴴ)*(V i U)ᴴ)*(E i)ᴴ := by
    rw [tensorPower_mul,tensorPower_mul,tensorPower_mul,tensorPower_star,tensorPower_star,
      ← coordinateTensorMatrix_eq_tensorPower]
    rw [Matrix.mul_assoc (tensorPower n U.val),coordinateTensorMatrix_support_expansion L hL hspan k,
      Matrix.sum_mul,Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Matrix.mul_assoc] using sandwich_intertwines _ (E i) (V i U) (Q i*(Q i)ᴴ)
      (((L.get i).coordinateLift k).embeddingMatrix_intertwines U)
  rw [coordinateHaarMarginal,partialTrace_rectangularHaarMoment]
  simp_rw [he]
  rw [integral_finset_sum _ (fun i hi => hint i)]
  apply Finset.sum_congr rfl
  intro i hi
  have hh := (rectangularSandwichCLM (E i)).integral_comp_comm
    (integrable_partitionSandwich (padPartition (L.get i).weight k)
      (padPartition_antitone _ (L.get i).weight_antitone k) (Q i*(Q i)ᴴ))
  change (∫ U, E i*(V i U*(Q i*(Q i)ᴴ)*(V i U)ᴴ)*(E i)ᴴ ∂unitaryHaar)=_
  change (∫ U, E i*(V i U*(Q i*(Q i)ᴴ)*(V i U)ᴴ)*(E i)ᴴ ∂unitaryHaar)=
    E i*(partitionTwirl (padPartition (L.get i).weight k)
      (padPartition_antitone _ (L.get i).weight_antitone k) (Q i*(Q i)ᴴ))*(E i)ᴴ at hh
  rw [hh,partitionTwirl_eq]
  have htr : (Q i*(Q i)ᴴ).trace=(partitionDimension (L.get i).weight (L.get i).weight_antitone : ℂ) := by
    rw [Matrix.trace_mul_comm,rankSectorMatrix_isometry,Matrix.trace_one,Fintype.card_fin]
  simp only [htr,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,E]

/-- Every induced ambient copy is an eigenspace of the actual Haar marginal. -/
theorem coordinateHaarMarginal_mul_liftEmbedding (k : ℕ) (j : Fin L.length) :
    coordinateHaarMarginal n r k*(L.get j).liftEmbeddingMatrix k=
      ((partitionDimension (L.get j).weight (L.get j).weight_antitone : ℂ)/
        (partitionDimension (padPartition (L.get j).weight k)
          (padPartition_antitone _ (L.get j).weight_antitone k) : ℂ)) •
        (L.get j).liftEmbeddingMatrix k := by
  rw [coordinateHaarMarginal_eq_blocks L hL hspan k]
  exact sum_weighted_projectors_mul (fun i : Fin L.length => (L.get i).liftEmbeddingMatrix k)
    (fun i => ((L.get i).coordinateLift k).embeddingMatrix_isometry)
    (embeddingMatrix_orthogonal (fun i : Fin L.length => (L.get i).coordinateLift k)
      (coordinateLift_family_orthogonal (fun i : Fin L.length => L.get i) hL k)) _ j

/-- No inverse on the null space is used: the actual spectral normalizer
has the exact positive dimension-ratio action on each supported copy. -/
theorem coordinateHaarNormalizer_mul_liftEmbedding (k : ℕ) (j : Fin L.length) :
    momentNormalizer (coordinateHaarMarginal n r k) (coordinateHaarMarginal_posSemidef n r k)*
      (L.get j).liftEmbeddingMatrix k=
      (rankMomentScale (L.get j).weight (L.get j).weight_antitone k : ℂ) •
        (L.get j).liftEmbeddingMatrix k := by
  have hh := momentNormalizer_mul_isometry (coordinateHaarMarginal n r k)
    (coordinateHaarMarginal_posSemidef n r k) ((L.get j).liftEmbeddingMatrix k)
    (((L.get j).coordinateLift k).embeddingMatrix_isometry)
    ((partitionDimension (L.get j).weight (L.get j).weight_antitone : ℝ)/
      (partitionDimension (padPartition (L.get j).weight k)
        (padPartition_antitone _ (L.get j).weight_antitone k) : ℝ))
    (by simpa only [Complex.ofReal_div,Complex.ofReal_natCast] using
      coordinateHaarMarginal_mul_liftEmbedding L hL hspan k j)
  rw [← Complex.ofReal_inv,← Real.sqrt_inv,inv_div] at hh
  exact hh

end Cloning.PCTRankPurification
