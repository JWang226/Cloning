import Cloning.TensorGibbsPhysicalLANUniform
import Cloning.TensorLANEmbeddingSchurState

/-! Exact identification of the normalized physical Schur block with the
rotated sector state used by the proven two-way Gibbs approximation. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open NormedSpace
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.TensorLocalUnitary Cloning.PCTLocalChart
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem canonicalRotatedGibbs_eq_sectorDisplacedGibbs (H : PhysicalHighestTensor n d)
    (r p : Fin d → ℝ) (t : ℝ) (z : PositiveRoot d → ℂ) :
    canonicalRotatedGibbs H (exp (t • orbitalGenerator p z)) r =
      sectorDisplacedGibbs (partitionHighestTensor H.weight H.weight_antitone) H.weight
        (partitionHighestTensor_cartan H.weight H.weight_antitone)
        (partitionHighestTensor_raising_zero H.weight H.weight_antitone) r p t z := rfl

/-- The literal sample size of the Schur copy agrees with the sum of its
highest weight, so its local unitary has exactly the scale used in LAN. -/
theorem canonicalRotatedGibbs_eq_partitionPhysicalGibbs (H : PhysicalHighestTensor n d)
    (r p : Fin d → ℝ) (z : PositiveRoot d → ℂ) :
    canonicalRotatedGibbs H (exp (sampleScale n • orbitalGenerator p z)) r =
      partitionPhysicalGibbs H.weight H.weight_antitone r p z := by
  rw [canonicalRotatedGibbs_eq_sectorDisplacedGibbs]
  unfold partitionPhysicalGibbs
  have he : sampleScale (∑ a, H.weight a) = sampleScale n := congrArg sampleScale H.weight_sum
  rw [he]

end Cloning.TensorLAN
