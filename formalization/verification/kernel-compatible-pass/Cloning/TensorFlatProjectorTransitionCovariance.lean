import Cloning.TensorFlatProjectorRankLaw
import Cloning.TensorFlatProjectorMoments
import Cloning.TensorFlatProjectorMixture
import Cloning.TensorFlatProjectorStateFidelity
import Cloning.TensorCloningSectorCovariance

/-! Flat physical transition fidelity on the complete unitary orbit. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m d r : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem copySectorPositive_unitary (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    copySectorPositive H U p hp =
      (copySectorPositive H 1 p hp).map
        (QuantumChannel.ofIsometry (copySectorUnitary H U hU).toLinearIsometry).toPositiveTracePreservingMap := by
  apply Subtype.ext
  change canonicalRotatedGibbs H U p =
    conjugationLinearMap (copySectorUnitary H U hU).toLinearIsometry.toContinuousLinearMap
      (canonicalRotatedGibbs H 1 p)
  rw [canonicalRotatedGibbs_one]
  rfl

/-- The actual conditional transition payoff is constant on the whole
physical unitary orbit, for every admissible finite Cartan transition. -/
theorem nonnegativeTransitionFidelity_unitary (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (i : SchurCopy n d) (j : SchurCopy m d)
    (hc : PartitionCompatible ((recursivePhysicalDecomposition n d).get i).weight
      ((recursivePhysicalDecomposition m d).get j).weight) :
    nonnegativeTransitionFidelity p hp U i j = nonnegativeTransitionFidelity p hp 1 i j := by
  let A := (recursivePhysicalDecomposition n d).get i
  let B := (recursivePhysicalDecomposition m d).get j
  let C := partitionTransitionChannel A.weight B.weight A.weight_antitone B.weight_antitone
  let V := QuantumChannel.ofIsometry (copySectorUnitary B U hU).toLinearIsometry
  have he : (copySectorPositive A U p hp).map C.toPositiveTracePreservingMap =
      ((copySectorPositive A 1 p hp).map C.toPositiveTracePreservingMap).map V.toPositiveTracePreservingMap := by
    rw [copySectorPositive_unitary A U hU p hp]
    apply Subtype.ext
    exact partitionTransitionChannel_covariant A.weight B.weight A.weight_antitone B.weight_antitone hc U hU
      (copySectorPositive A 1 p hp).1
  change ((copySectorPositive A U p hp).map C.toPositiveTracePreservingMap).rootFidelity
    (copySectorPositive B U p hp) =
    ((copySectorPositive A 1 p hp).map C.toPositiveTracePreservingMap).rootFidelity (copySectorPositive B 1 p hp)
  rw [he, copySectorPositive_unitary B U hU p hp]
  exact rootFidelity_map_isometryEquiv (copySectorUnitary B U hU) _ _


theorem padPartition_compatible (mu lam : Fin r → ℕ)
    (hc : PartitionCompatible mu lam) (k : ℕ) :
    PartitionCompatible (padPartition mu k) (padPartition lam k) := by
  constructor
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro i
      simpa only [padPartition,Fin.append_left] using hc.1 i
    · intro i; simp [padPartition]
  · have he : (fun a => padPartition lam k a-padPartition mu k a) =
        padPartition (fun a => lam a-mu a) k := by
      funext a
      refine Fin.addCases ?_ ?_ a <;> intro i <;> simp [padPartition]
    rw [he]
    exact padPartition_antitone _ hc.2 k

/-- Copy labels determine the physical conditional fidelity at the identity. -/
theorem nonnegativeTransitionFidelity_one_eq (p : Fin d → ℝ) (hp : ∀a,0≤p a)
    (i : SchurCopy n d) (j : SchurCopy m d) :
    nonnegativeTransitionFidelity p hp 1 i j =
      ((nonnegativePartitionGibbsPositive ((recursivePhysicalDecomposition n d).get i).weight
        ((recursivePhysicalDecomposition n d).get i).weight_antitone p hp).map
        (partitionTransitionChannel ((recursivePhysicalDecomposition n d).get i).weight
          ((recursivePhysicalDecomposition m d).get j).weight
          ((recursivePhysicalDecomposition n d).get i).weight_antitone
          ((recursivePhysicalDecomposition m d).get j).weight_antitone).toPositiveTracePreservingMap).rootFidelity
        (nonnegativePartitionGibbsPositive ((recursivePhysicalDecomposition m d).get j).weight
          ((recursivePhysicalDecomposition m d).get j).weight_antitone p hp) := by
  have hstate (H : PhysicalHighestTensor n d) : copySectorPositive H 1 p hp =
      nonnegativePartitionGibbsPositive H.weight H.weight_antitone p hp := by
    apply Subtype.ext
    exact canonicalRotatedGibbs_one H p
  have hstate' (H : PhysicalHighestTensor m d) : copySectorPositive H 1 p hp =
      nonnegativePartitionGibbsPositive H.weight H.weight_antitone p hp := by
    apply Subtype.ext
    exact canonicalRotatedGibbs_one H p
  simp only [nonnegativeTransitionFidelity,hstate,hstate']

def weightTransitionFidelity (p : Fin d → ℝ) (hp : ∀a,0≤p a)
    (mu lam : Fin d → ℕ) : ℝ :=
  if hm : Antitone mu then
    if hl : Antitone lam then
      ((nonnegativePartitionGibbsPositive _ hm p hp).map
        (partitionTransitionChannel _ _ hm hl).toPositiveTracePreservingMap).rootFidelity
        (nonnegativePartitionGibbsPositive _ hl p hp)
    else 0
  else 0

def labelTransitionFidelity (p : Fin d → ℝ) (hp : ∀a,0≤p a)
    (mu : Cloning.YoungGeneral.Shape d n) (lam : Cloning.YoungGeneral.Shape d m) : ℝ :=
  weightTransitionFidelity p hp (fun a => (mu a).val) (fun a => (lam a).val)

theorem labelTransitionFidelity_copy (p : Fin d → ℝ) (hp : ∀a,0≤p a)
    (i : SchurCopy n d) (j : SchurCopy m d) :
    labelTransitionFidelity p hp ((recursivePhysicalDecomposition n d).get i).shape
      ((recursivePhysicalDecomposition m d).get j).shape =
      nonnegativeTransitionFidelity p hp 1 i j := by
  rw [nonnegativeTransitionFidelity_one_eq]
  simp only [labelTransitionFidelity,weightTransitionFidelity,PhysicalHighestTensor.shape,
    dif_pos ((recursivePhysicalDecomposition n d).get i).weight_antitone,
    dif_pos ((recursivePhysicalDecomposition m d).get j).weight_antitone]

theorem padPartition_compatible_iff (mu lam : Fin r → ℕ) (k : ℕ) :
    PartitionCompatible (padPartition mu k) (padPartition lam k) ↔ PartitionCompatible mu lam := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [padPartition,Fin.append_left] using h.1 (Fin.castAdd k i)
    · intro i j hij
      simpa only [padPartition,Fin.append_left] using h.2 (show Fin.castAdd k i ≤ Fin.castAdd k j from hij)
  · exact fun h => padPartition_compatible mu lam h k

theorem labelTransitionFidelity_pad (mu : Cloning.YoungGeneral.Shape r n)
    (lam : Cloning.YoungGeneral.Shape r m) (hmu : Antitone (fun a => (mu a).val))
    (hlam : Antitone (fun a => (lam a).val))
    (hc : PartitionCompatible (fun a => (mu a).val) (fun a => (lam a).val))
    (k : ℕ) (hr : 0<r) :
    labelTransitionFidelity (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k)
      (padShape mu k) (padShape lam k) =
      Real.sqrt (Cloning.YoungDimensionRatio.dimensionRatio r k (Cloning.YoungGeneral.shapeRows mu) /
        Cloning.YoungDimensionRatio.dimensionRatio r k (Cloning.YoungGeneral.shapeRows lam)) := by
  unfold labelTransitionFidelity
  rw [padShape_val,padShape_val]
  simp only [weightTransitionFidelity,dif_pos (padPartition_antitone _ hmu k),
    dif_pos (padPartition_antitone _ hlam k)]
  exact partitionTransition_rankFlat_fidelity _ _ hmu hlam hc k hr

end Cloning.TensorCloning
