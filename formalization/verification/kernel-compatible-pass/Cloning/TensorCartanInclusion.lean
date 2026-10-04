import Cloning.TensorCartanProduct
import Cloning.TensorHighestGramIsometry

/-! A literal physical Cartan inclusion for arbitrary partitions. Its source
is the constructed cyclic highest sector of the sum weight; its target is
the tensor-product subspace of the two physical cyclic sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem sumPartition_antitone (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    Antitone (fun i => mu i + nu i) :=
  fun _ _ hij => Nat.add_le_add (hmu hij) (hnu hij)

def cartanHighest (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d) :=
  tensorJoin (partitionHighestTensor mu hmu) (partitionHighestTensor nu hnu)

theorem cartanHighest_norm (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    ‖cartanHighest mu nu hmu hnu‖ = 1 :=
  tensorJoin_norm_one _ _ (partitionHighestTensor_norm mu hmu) (partitionHighestTensor_norm nu hnu)

theorem cartanHighest_raising_zero (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (a b : Fin d) (hab : a < b) :
    collectiveGenerator ((∑ i, mu i) + ∑ i, nu i) a b (cartanHighest mu nu hmu hnu) = 0 :=
  tensorJoin_raising_zero a b _ _ (partitionHighestTensor_raising_zero mu hmu a b hab)
    (partitionHighestTensor_raising_zero nu hnu a b hab)

theorem cartanHighest_cartan (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (a : Fin d) :
    collectiveGenerator ((∑ i, mu i) + ∑ i, nu i) a a (cartanHighest mu nu hmu hnu) =
      ((mu a + nu a : ℕ) : ℂ) • cartanHighest mu nu hmu hnu := by
  simpa only [Nat.cast_add] using tensorJoin_cartan a
    (partitionHighestTensor mu hmu) (partitionHighestTensor nu hnu)
    (mu a : ℂ) (nu a : ℂ) (partitionHighestTensor_cartan mu hmu a)
    (partitionHighestTensor_cartan nu hnu a)

/-- The sum-weight sector is exactly isometric to the cyclic subspace generated
by the literal product of the two highest tensors. -/
def cartanCyclicIsometry (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    cyclicSector (partitionHighestTensor (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu))
      ≃ₗᵢ[ℂ] cyclicSector (cartanHighest mu nu hmu hnu) :=
  highestCyclicIsometry _ _ (fun i => ((mu i + nu i : ℕ) : ℂ))
    (partitionHighestTensor_cartan _ _) (cartanHighest_cartan mu nu hmu hnu)
    (partitionHighestTensor_raising_zero _ _) (cartanHighest_raising_zero mu nu hmu hnu)
    (partitionHighestTensor_norm _ _) (cartanHighest_norm mu nu hmu hnu)

/-- The physical Cartan inclusion is an actual linear isometry into the literal
tensor-product subspace. No abstract intertwiner is supplied as a premise. -/
def cartanInclusion (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    cyclicSector (partitionHighestTensor (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu))
      →ₗᵢ[ℂ] tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
        (cyclicSector (partitionHighestTensor nu hnu)) :=
  (sectorInclusionIsometry (cyclicSector_tensorJoin_le
    (partitionHighestTensor mu hmu) (partitionHighestTensor nu hnu)
    (fun i => (mu i : ℂ)) (fun i => (nu i : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_cartan nu hnu)
    (partitionHighestTensor_raising_zero mu hmu) (partitionHighestTensor_raising_zero nu hnu))).comp
      (cartanCyclicIsometry mu nu hmu hnu).toLinearIsometry

theorem cartanInclusion_loweringWord
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (w : List (PositiveRoot d)) :
    (cartanInclusion mu nu hmu hnu
      ⟨loweringWord (partitionHighestTensor (fun i => mu i + nu i)
        (sumPartition_antitone mu nu hmu hnu)) w, loweringWord_mem_cyclicSector _ w⟩ :
        TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)) =
      loweringWord (cartanHighest mu nu hmu hnu) w := by
  exact highestCyclicIsometry_loweringWord _ _ (fun i => ((mu i + nu i : ℕ) : ℂ))
    (partitionHighestTensor_cartan _ _) (cartanHighest_cartan mu nu hmu hnu)
    (partitionHighestTensor_raising_zero _ _) (cartanHighest_raising_zero mu nu hmu hnu)
    (partitionHighestTensor_norm _ _) (cartanHighest_norm mu nu hmu hnu) w

/-- The selected phase of the Cartan inclusion sends the normalized sum highest
vector to the exact tensor product of the two normalized highest vectors. -/
theorem cartanInclusion_highest
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    (cartanInclusion mu nu hmu hnu
      ⟨partitionHighestTensor (fun i => mu i + nu i) (sumPartition_antitone mu nu hmu hnu),
        highest_mem_cyclicSector _⟩ : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)) =
      tensorJoin (partitionHighestTensor mu hmu) (partitionHighestTensor nu hnu) :=
  cartanInclusion_loweringWord mu nu hmu hnu []

end Cloning.TensorLie
