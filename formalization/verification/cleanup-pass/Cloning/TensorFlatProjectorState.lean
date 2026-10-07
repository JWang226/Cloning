import Cloning.TensorFlatProjectorSectorSupport

/-! Actual rank-r support projections and flat-sector densities in ambient dimension r+k. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The literal polynomial action of the coordinate support projection. -/
def partitionSupportOperator (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :=
  cyclicTensorOperator
    (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
    (fun a => (padPartition mu k a : ℂ))
    (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _)
    (coordinateSupportMatrix r k)

theorem rankSectorEmbedding_adjoint_transport (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (x : cyclicSector (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))) :
    (rankSectorEmbedding mu hmu k).toContinuousLinearMap.adjoint x =
      (coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu)).toContinuousLinearMap.adjoint
        (rankHighestIsometry mu hmu k x) := by
  apply ext_inner_left ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  change ⟪rankSectorEmbedding mu hmu k z,x⟫_ℂ =
    ⟪coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu) z,
      rankHighestIsometry mu hmu k x⟫_ℂ
  rw [← (rankHighestIsometry mu hmu k).inner_map_map, rankHighestIsometry_embedding]

/-- The support operator is the range projection of the constructed rank inclusion. -/
theorem partitionSupportOperator_eq_rangeProjection (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    partitionSupportOperator mu hmu k =
      (rankSectorEmbedding mu hmu k).toContinuousLinearMap.comp
        (rankSectorEmbedding mu hmu k).toContinuousLinearMap.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply (rankHighestIsometry mu hmu k).injective
  have he := highestCyclicIsometry_tensorOperator
    (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
    (rankEmbeddedHighest mu hmu k) (fun a => (padPartition mu k a : ℂ))
    (partitionHighestTensor_cartan _ _) (rankEmbeddedHighest_weight mu hmu k)
    (partitionHighestTensor_raising_zero _ _) (rankEmbeddedHighest_raise mu hmu k)
    (partitionHighestTensor_norm _ _) (rankEmbeddedHighest_norm mu hmu k)
    (coordinateSupportMatrix r k) x
  change rankHighestIsometry mu hmu k (partitionSupportOperator mu hmu k x) = _ at he
  rw [he]
  change cyclicTensorOperator (coordinateTensorEmbedding _ r k (partitionHighestTensor mu hmu))
    (fun a => (padPartition mu k a : ℂ))
    (coordinateTensorEmbedding_highest (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)).1
    (coordinateTensorEmbedding_highest (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)).2
    (coordinateSupportMatrix r k) (rankHighestIsometry mu hmu k x) =
      rankHighestIsometry mu hmu k
        (rankSectorEmbedding mu hmu k ((rankSectorEmbedding mu hmu k).toContinuousLinearMap.adjoint x))
  have hs := coordinateSectorEmbedding_support (k := k)
    (partitionHighestTensor mu hmu) mu (partitionHighestTensor_cartan mu hmu)
    (partitionHighestTensor_raising_zero mu hmu)
  have hsx := congrArg (fun T => T (rankHighestIsometry mu hmu k x)) hs
  apply hsx.trans
  change coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu)
    ((coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu)).toContinuousLinearMap.adjoint
      (rankHighestIsometry mu hmu k x)) = _
  exact (congrArg (coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu))
    (rankSectorEmbedding_adjoint_transport mu hmu k x).symm).trans
      (rankHighestIsometry_embedding mu hmu k _).symm

/-- Exact rank of the physical ambient support projector. -/
theorem trace_partitionSupportOperator (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    LinearMap.trace ℂ _ (partitionSupportOperator mu hmu k).toLinearMap =
      (partitionDimension mu hmu : ℂ) := by
  rw [partitionSupportOperator_eq_rangeProjection]
  let J := (rankSectorEmbedding mu hmu k).toContinuousLinearMap
  change LinearMap.trace ℂ _ (J.toLinearMap.comp J.adjoint.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  have he : J.adjoint.comp J = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mp (rankSectorEmbedding mu hmu k).norm_map
  change LinearMap.trace ℂ _ (J.adjoint.comp J).toLinearMap = _
  rw [he]
  exact LinearMap.trace_id ℂ _

/-- Literal homogeneous scaling of the tensor operator, including c=0. -/
theorem tensorOperator_smul {n d : ℕ} (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorOperator n (c • X) = c^n • tensorOperator n X := by
  ext x w
  simp only [tensorOperator_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ContinuousLinearMap.smul_apply,
    lp.coeFn_smul, Pi.smul_apply]
  simp only [Finset.mul_sum, mul_assoc]

def rankFlatSpectrum (r k : ℕ) : Fin (r+k) → ℝ := fun a =>
  if a.val < r then 1/(r:ℝ) else 0

theorem rankFlatSpectrum_nonneg (r k : ℕ) (a : Fin (r+k)) : 0 ≤ rankFlatSpectrum r k a := by
  unfold rankFlatSpectrum
  split_ifs <;> positivity

/-- The ambient flat operator is the actual supported identity, with tensor normalization. -/
theorem sectorGibbsOperator_rankFlat (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    sectorGibbsOperator
      (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
      (padPartition mu k) (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _)
      (rankFlatSpectrum r k) =
    (((1/(r:ℝ))^(∑ a,mu a) : ℝ) : ℂ) • partitionSupportOperator mu hmu k := by
  have hm : Matrix.diagonal (fun a => (rankFlatSpectrum r k a : ℂ)) =
      ((1/(r:ℝ):ℝ):ℂ) • coordinateSupportMatrix r k := by
    rw [coordinateSupportMatrix, ← Matrix.diagonal_smul]
    congr 1
    funext a
    simp only [rankFlatSpectrum, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change tensorOperator _ (Matrix.diagonal _) (x : TensorRegister (∑ a,padPartition mu k a) (Fin (r+k))) =
    (((1/(r:ℝ))^(∑ a,mu a) : ℝ) : ℂ) • tensorOperator _ (coordinateSupportMatrix r k) (x : TensorRegister (∑ a,padPartition mu k a) (Fin (r+k)))
  rw [hm, tensorOperator_smul, ContinuousLinearMap.smul_apply]
  simp only [sum_padPartition, Complex.ofReal_pow]

/-- Exact ambient flat character: support dimension divided by r^N. -/
theorem physicalSectorCharacter_rankFlat (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    physicalSectorCharacter (padPartition mu k) (rankFlatSpectrum r k) =
      (partitionDimension mu hmu : ℝ) / (r:ℝ)^(∑ a,mu a) := by
  simp only [physicalSectorCharacter, dif_pos (padPartition_antitone mu hmu k)]
  rw [sectorPartitionFunction_eq_linearMapTrace _ _ _ _ _ (rankFlatSpectrum_nonneg r k),
    sectorGibbsOperator_rankFlat]
  change (LinearMap.trace ℂ _ ((((1/(r:ℝ))^(∑ a,mu a) : ℝ) : ℂ) •
    (partitionSupportOperator mu hmu k).toLinearMap)).re = _
  rw [map_smul, trace_partitionSupportOperator]
  simp only [smul_eq_mul]
  have hc : ((((1/(r:ℝ))^(∑ a,mu a) : ℝ) : ℂ) *
      (partitionDimension mu hmu : ℂ)).re =
      (1/(r:ℝ))^(∑ a,mu a) * (partitionDimension mu hmu : ℝ) := by norm_cast
  rw [hc, one_div_pow]
  ring

end Cloning.TensorLie
