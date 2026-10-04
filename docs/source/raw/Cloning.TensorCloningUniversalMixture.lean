import Cloning.TensorCloningAchievabilityMixture
import Cloning.TensorCloningCopyAffinity
import Cloning.InfiniteFidelityTransitionWeights
import Cloning.YoungPhysicalRounding

/-! A finite lower bound for the actual spectrum-independent cloner. The
classical factor is exactly the physical randomized Young-label affinity. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix Topology
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.Hybrid Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.YoungCompatibility Cloning.YoungHyperplane Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def universalJointWeight (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1)) : ℝ :=
  knownCopyWeight n (d+1) p i * probability (universalCopyPMF n m d i) j

theorem universalJointWeight_nonneg (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1)) :
    0 ≤ universalJointWeight n m d p i j :=
  mul_nonneg (knownCopyWeight_nonneg _ _ _ _) ENNReal.toReal_nonneg

theorem universalJointWeight_marginal (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (j : SchurCopy m (d+1)) :
    (∑ i, universalJointWeight n m d p i j) =
      probability (universalOutputCopyPMF n m d p hp hs) j := by
  rw [universalOutputCopyPMF, probability_bind, tsum_fintype]
  simp only [universalJointWeight, probability, physicalCopyPMF_toReal, knownCopyWeight]

theorem universalChannel_rotated_apply (n m d : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ a, 0 < p a) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (universalChannel n m d).toLinearMap
      (matrixTensorPower (U * Matrix.diagonal (fun a ↦ (p a : ℂ)) * Uᴴ) n) =
      ∑ ij : SchurCopy n (d+1) × SchurCopy m (d+1),
        (universalJointWeight n m d p ij.1 ij.2 : ℂ) •
          (copyTransition n m (d+1) ij.1 ij.2).toLinearMap
            (canonicalRotatedGibbs ((recursivePhysicalDecomposition n (d+1)).get ij.1) U p) := by
  rw [universalChannel, channel_apply]
  simp only [matrixTensorPower_canonical_block, canonicalTensorWeight_rotated_diagonal _ U p hp,
    map_smul, Fintype.sum_prod_type, universalJointWeight, probability, Complex.ofReal_mul, mul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact smul_comm _ _ _

/-- The actual universal channel's global fidelity dominates the full physical
Young affinity times any retained sector bound, minus the square root of the
actual discarded joint probability. -/
theorem universalChannel_payoff_lower {d : ℕ} (n m : ℕ)
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (keep : SchurCopy n (d+1) → SchurCopy m (d+1) → Prop)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hgood : ∀ i j, keep i j → c ≤ transitionFidelity n m (d+1) p.eigenvalue p.positive U i j) :
    c * CountableScheffe.affinity
      (probability (tensorYoungFallbackOutput d n m ((m : ℝ)/(n : ℝ)) p.eigenvalue
        (fun a ↦ (p.positive a).le) p.normalized))
      (probability (tensorYoungIntegerPMF d m p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized)) -
      Real.sqrt (∑ ij : SchurCopy n (d+1) × SchurCopy m (d+1),
        if keep ij.1 ij.2 then 0 else universalJointWeight n m d p.eigenvalue ij.1 ij.2) ≤
      spectrumPayoff n m (universalChannel n m d) p U := by
  let A (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1)) :=
    (copySectorState ((recursivePhysicalDecomposition n (d+1)).get i) U p.eigenvalue p.positive).map
      (copyTransition n m (d+1) i j).toPositiveTracePreservingMap
  let B (j : SchurCopy m (d+1)) :=
    (copySectorState ((recursivePhysicalDecomposition m (d+1)).get j) U p.eigenvalue p.positive).map
      (QuantumChannel.ofIsometry ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding).toPositiveTracePreservingMap
  have hmono (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1)) :
      transitionFidelity n m (d+1) p.eigenvalue p.positive U i j ≤ (A i j).rootFidelity (B j) := by
    let C := (recursivePhysicalDecomposition n (d+1)).get i
    let D := (recursivePhysicalDecomposition m (d+1)).get j
    let S := (copySectorState C U p.eigenvalue p.positive).map
      (partitionTransitionChannel C.weight D.weight C.weight_antitone D.weight_antitone).toPositiveTracePreservingMap
    let T := copySectorState D U p.eigenvalue p.positive
    exact InfiniteFidelity.fidelity_data_processing
      (QuantumChannel.ofIsometry D.canonicalEmbedding) S.1 T.1 S.2 T.2
  have hl := PositiveTraceClass.transition_rootFidelity_lower
    (universalJointWeight n m d p.eigenvalue) (knownCopyWeight m (d+1) p.eigenvalue)
    (universalJointWeight_nonneg n m d p.eigenvalue) (knownCopyWeight_nonneg _ _ _)
    (knownCopyWeight_sum m (d+1) p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized).le
    A B keep c hc0 hc1 (fun i j h ↦ (hgood i j h).trans (hmono i j))
  have hA : PositiveTraceClass.finiteMixture
      (fun ij : SchurCopy n (d+1) × SchurCopy m (d+1) ↦ universalJointWeight n m d p.eigenvalue ij.1 ij.2)
      (fun ij ↦ universalJointWeight_nonneg n m d p.eigenvalue ij.1 ij.2) (fun ij ↦ A ij.1 ij.2) =
      (tensorState (orbitState p U) n).map (universalChannel n m d).toPositiveTracePreservingMap := by
    apply Subtype.ext
    symm
    exact universalChannel_rotated_apply n m d p.eigenvalue p.positive U
  have hB : PositiveTraceClass.finiteMixture (knownCopyWeight m (d+1) p.eigenvalue)
      (knownCopyWeight_nonneg _ _ _) B = tensorState (orbitState p U) m := by
    apply Subtype.ext
    symm
    exact matrixTensorPower_rotated_eq_copy_mixture (n := m) (d := d+1) U p.eigenvalue p.positive
  rw [hA, hB] at hl
  have ha : (∑ j, Real.sqrt (∑ i, universalJointWeight n m d p.eigenvalue i j) *
      Real.sqrt (knownCopyWeight m (d+1) p.eigenvalue j)) =
      CountableScheffe.affinity
        (probability (tensorYoungFallbackOutput d n m ((m : ℝ)/(n : ℝ)) p.eigenvalue
          (fun a ↦ (p.positive a).le) p.normalized))
        (probability (tensorYoungIntegerPMF d m p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized)) := by
    rw [← universalOutputCopyPMF_affinity n m d p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized]
    simp only [CountableScheffe.affinity, tsum_fintype,
      universalJointWeight_marginal n m d p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized,
      probability, physicalCopyPMF_toReal, knownCopyWeight]
  rw [ha] at hl
  exact hl

end Cloning.TensorCloning
