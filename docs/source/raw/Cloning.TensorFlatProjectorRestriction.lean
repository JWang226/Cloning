import Cloning.TensorFlatProjectorSector
import Cloning.TensorHighestGramCovariance

/-! Canonical physical rank restriction, with its phase fixed on highest tensors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ}

/-- A concrete full-ambient highest tensor supported on the first r letters. -/
def rankEmbeddedHighest (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    TensorRegister (∑ a, mu a) (Fin (r+k)) :=
  coordinateTensorEmbedding (∑ a, mu a) r k (partitionHighestTensor mu hmu)

theorem rankEmbeddedHighest_norm (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    ‖rankEmbeddedHighest mu hmu k‖ = 1 := by
  rw [rankEmbeddedHighest, LinearIsometry.norm_map, partitionHighestTensor_norm]

theorem rankEmbeddedHighest_weight (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (a : Fin (r+k)) :
    collectiveGenerator (∑ i,mu i) a a (rankEmbeddedHighest mu hmu k) =
      (padPartition mu k a : ℂ) • rankEmbeddedHighest mu hmu k :=
  (coordinateTensorEmbedding_highest (partitionHighestTensor mu hmu) mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)).1 a

theorem rankEmbeddedHighest_raise (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (a b : Fin (r+k)) (hab : a < b) :
    collectiveGenerator (∑ i,mu i) a b (rankEmbeddedHighest mu hmu k) = 0 :=
  (coordinateTensorEmbedding_highest (partitionHighestTensor mu hmu) mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)).2 a b hab

/-- Exact Gram transport identifies the canonical ambient copy with the
explicit supported-highest copy. -/
def rankHighestIsometry (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    cyclicSector (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k)) ≃ₗᵢ[ℂ]
      cyclicSector (rankEmbeddedHighest mu hmu k) :=
  highestCyclicIsometry _ _ (fun a => (padPartition mu k a : ℂ))
    (partitionHighestTensor_cartan _ _) (rankEmbeddedHighest_weight mu hmu k)
    (partitionHighestTensor_raising_zero _ _) (rankEmbeddedHighest_raise mu hmu k)
    (partitionHighestTensor_norm _ _) (rankEmbeddedHighest_norm mu hmu k)

/-- The actual rank-r sector embeds isometrically in its ambient counterpart. -/
def rankSectorEmbedding (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    cyclicSector (partitionHighestTensor mu hmu) →ₗᵢ[ℂ]
      cyclicSector (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k)) :=
  (rankHighestIsometry mu hmu k).symm.toLinearIsometry.comp
    (coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu))

@[simp] theorem rankHighestIsometry_embedding (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (x : cyclicSector (partitionHighestTensor mu hmu)) :
    rankHighestIsometry mu hmu k (rankSectorEmbedding mu hmu k x) =
      coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu) x :=
  (rankHighestIsometry mu hmu k).apply_symm_apply _

/-- Rank restriction agrees on every genuine lowering word. -/
theorem rankSectorEmbedding_loweringWord (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (w : List (PositiveRoot r)) :
    (rankSectorEmbedding mu hmu k
      ⟨loweringWord (partitionHighestTensor mu hmu) w, loweringWord_mem_cyclicSector _ w⟩ :
      TensorRegister (∑ a, padPartition mu k a) (Fin (r+k))) =
      loweringWord (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
        (w.map coordinateRoot) := by
  have he := highestCyclicIsometry_loweringWord
    (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
    (rankEmbeddedHighest mu hmu k) (fun a => (padPartition mu k a : ℂ))
    (partitionHighestTensor_cartan _ _) (rankEmbeddedHighest_weight mu hmu k)
    (partitionHighestTensor_raising_zero _ _) (rankEmbeddedHighest_raise mu hmu k)
    (partitionHighestTensor_norm _ _) (rankEmbeddedHighest_norm mu hmu k) (w.map coordinateRoot)
  have he' : rankHighestIsometry mu hmu k
      ⟨loweringWord (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
        (w.map coordinateRoot), loweringWord_mem_cyclicSector _ _⟩ =
      coordinateSectorEmbedding (k := k) (partitionHighestTensor mu hmu)
        ⟨loweringWord (partitionHighestTensor mu hmu) w,loweringWord_mem_cyclicSector _ _⟩ := by
    apply Subtype.ext
    exact he.trans (coordinateTensorEmbedding_loweringWord _ w).symm
  have hh := (rankHighestIsometry mu hmu k).injective
    ((rankHighestIsometry_embedding mu hmu k _).trans he'.symm)
  exact congrArg Subtype.val hh

/-- Highest-vector phase normalization is proved, not chosen as a premise. -/
theorem rankSectorEmbedding_highest (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ) :
    (rankSectorEmbedding mu hmu k
      ⟨partitionHighestTensor mu hmu, highest_mem_cyclicSector _⟩ :
      TensorRegister (∑ a, padPartition mu k a) (Fin (r+k))) =
      partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k) :=
  rankSectorEmbedding_loweringWord mu hmu k []

/-- Full supported-generator naturality of the canonical physical inclusion. -/
theorem rankSectorEmbedding_intertwines (mu : Fin r → ℕ) (hmu : Antitone mu) (k : ℕ)
    (a b : Fin r) (x : cyclicSector (partitionHighestTensor mu hmu)) :
    rankSectorEmbedding mu hmu k (partitionGenerator mu hmu a b x) =
      partitionGenerator (padPartition mu k) (padPartition_antitone mu hmu k)
        (Fin.castAdd k a) (Fin.castAdd k b) (rankSectorEmbedding mu hmu k x) := by
  apply (rankHighestIsometry mu hmu k).injective
  rw [rankHighestIsometry_embedding]
  have he := highestCyclicIsometry_intertwines
    (partitionHighestTensor (padPartition mu k) (padPartition_antitone mu hmu k))
    (rankEmbeddedHighest mu hmu k) (fun a => (padPartition mu k a : ℂ))
    (partitionHighestTensor_cartan _ _) (rankEmbeddedHighest_weight mu hmu k)
    (partitionHighestTensor_raising_zero _ _) (rankEmbeddedHighest_raise mu hmu k)
    (partitionHighestTensor_norm _ _) (rankEmbeddedHighest_norm mu hmu k)
    (Fin.castAdd k a) (Fin.castAdd k b) (rankSectorEmbedding mu hmu k x)
  change rankHighestIsometry mu hmu k
      (partitionGenerator (padPartition mu k) (padPartition_antitone mu hmu k)
        (Fin.castAdd k a) (Fin.castAdd k b) (rankSectorEmbedding mu hmu k x)) =
    cyclicGenerator (rankEmbeddedHighest mu hmu k) (fun a => (padPartition mu k a : ℂ))
      (rankEmbeddedHighest_weight mu hmu k) (rankEmbeddedHighest_raise mu hmu k)
      (Fin.castAdd k a) (Fin.castAdd k b)
      (rankHighestIsometry mu hmu k (rankSectorEmbedding mu hmu k x)) at he
  rw [he, rankHighestIsometry_embedding]
  apply Subtype.ext
  exact coordinateTensorEmbedding_collective (x : TensorRegister (∑ a,mu a) (Fin r)) a b

end Cloning.TensorLie
