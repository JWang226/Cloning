import Cloning.TensorCloningTransitionCovariance

/-! Conditional physical cloning fidelity is independent of the unknown
unitary eigenbasis whenever the chosen partition pair is compatible. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem canonicalRotatedGibbs_one (H : PhysicalHighestTensor n d) (p : Fin d → ℝ) :
    canonicalRotatedGibbs H (1 : Matrix (Fin d) (Fin d) ℂ) p = canonicalGibbsDensity H p := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  simp only [canonicalRotatedGibbs, PhysicalHighestTensor.canonicalTensorOperator,
    cyclicTensorOperator_one, conjugationLinearMap_coe, operatorConjugation_apply,
    ← ContinuousLinearMap.star_eq_adjoint, star_one, ContinuousLinearMap.one_apply]

def copySectorUnitary (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    H.CanonicalSector ≃ₗᵢ[ℂ] H.CanonicalSector :=
  cyclicUnitary (partitionHighestTensor H.weight H.weight_antitone) (fun a ↦ (H.weight a : ℂ))
    (partitionHighestTensor_cartan H.weight H.weight_antitone)
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone) U hU

theorem copySectorState_unitary (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    copySectorState H U p hp =
      (copySectorState H 1 p hp).map
        (QuantumChannel.ofIsometry (copySectorUnitary H U hU).toLinearIsometry).toPositiveTracePreservingMap := by
  apply Subtype.ext
  change canonicalRotatedGibbs H U p =
    conjugationLinearMap (copySectorUnitary H U hU).toLinearIsometry.toContinuousLinearMap
      (canonicalRotatedGibbs H 1 p)
  rw [canonicalRotatedGibbs_one]
  rfl

/-- The actual conditional transition payoff is constant on the whole
physical unitary orbit, for every admissible finite Cartan transition. -/
theorem transitionFidelity_unitary (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (i : SchurCopy n d) (j : SchurCopy m d)
    (hc : PartitionCompatible ((recursivePhysicalDecomposition n d).get i).weight
      ((recursivePhysicalDecomposition m d).get j).weight) :
    transitionFidelity n m d p hp U i j = transitionFidelity n m d p hp 1 i j := by
  let A := (recursivePhysicalDecomposition n d).get i
  let B := (recursivePhysicalDecomposition m d).get j
  let C := partitionTransitionChannel A.weight B.weight A.weight_antitone B.weight_antitone
  let V := QuantumChannel.ofIsometry (copySectorUnitary B U hU).toLinearIsometry
  have he : (copySectorState A U p hp).map C.toPositiveTracePreservingMap =
      ((copySectorState A 1 p hp).map C.toPositiveTracePreservingMap).map V.toPositiveTracePreservingMap := by
    rw [copySectorState_unitary A U hU p hp]
    apply Subtype.ext
    exact partitionTransitionChannel_covariant A.weight B.weight A.weight_antitone B.weight_antitone hc U hU
      (copySectorState A 1 p hp).1
  change ((copySectorState A U p hp).map C.toPositiveTracePreservingMap).rootFidelity
    (copySectorState B U p hp) =
    ((copySectorState A 1 p hp).map C.toPositiveTracePreservingMap).rootFidelity (copySectorState B 1 p hp)
  rw [he, copySectorState_unitary B U hU p hp]
  exact rootFidelity_map_isometryEquiv (copySectorUnitary B U hU) _ _

end Cloning.TensorCloning
