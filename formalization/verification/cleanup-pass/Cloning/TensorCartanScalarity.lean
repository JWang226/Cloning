import Cloning.TensorCartanCoordinates

/-! Scalar commutants in the actual finite coordinates of physical sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- Every coordinate matrix commuting with all actual root generators is scalar.
This is derived from the proved cyclic highest-line uniqueness. -/
theorem partitionGeneratorMatrix_commutant_scalar
    (mu : Fin d → ℕ) (hmu : Antitone mu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ)
    (hcomm : ∀ a b, M * partitionGeneratorMatrix mu hmu a b =
      partitionGeneratorMatrix mu hmu a b * M) :
    ∃ c : ℂ, M = c • (1 : Matrix (PartitionIndex mu hmu) (PartitionIndex mu hmu) ℂ) := by
  let B := (partitionBasis mu hmu).toBasis
  let T := Matrix.toLin B B M
  have hT : ∀ a b x, T (partitionGenerator mu hmu a b x) =
      partitionGenerator mu hmu a b (T x) := by
    intro a b x
    have he : T.comp (partitionGenerator mu hmu a b).toLinearMap =
        (partitionGenerator mu hmu a b).toLinearMap.comp T := by
      apply (LinearMap.toMatrix B B).injective
      rw [LinearMap.toMatrix_comp B B B, LinearMap.toMatrix_comp B B B]
      simp only [T, LinearMap.toMatrix_toLin]
      exact hcomm a b
    exact LinearMap.congr_fun he x

  obtain ⟨c, hc⟩ := cyclicGenerator_commutant_scalar (partitionHighestTensor mu hmu)
    (fun i => (mu i : ℂ)) (partitionHighestTensor_cartan mu hmu)
    (partitionHighestTensor_raising_zero mu hmu) (partitionHighestTensor_norm mu hmu) T hT
  refine ⟨c, ?_⟩
  have he := congrArg (LinearMap.toMatrix B B) hc
  simpa only [T, LinearMap.toMatrix_toLin, map_smul, LinearMap.toMatrix_id] using he

end Cloning.TensorLie
