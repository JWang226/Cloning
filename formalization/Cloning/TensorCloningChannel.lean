import Cloning.InfiniteFiniteInstrument
import Cloning.TensorCartanChannel
import Cloning.TensorLANEmbeddingSchur
import Cloning.TensorSchurDecompositionTrace
import Cloning.TensorCloningGlobalCovarianceState

/-! Concrete global cloning channels on the physical tensor registers.
The channel measures the exhaustive Schur decomposition, applies the actual
Cartan sector channel whenever the partition difference is admissible, and
samples the output physical copy with a normalized classical row. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def PartitionCompatible {d : ℕ} (μ ν : Fin d → ℕ) : Prop :=
  (∀ i, μ i ≤ ν i) ∧ Antitone (fun i ↦ ν i - μ i)

def partitionHighestState {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) :
    DensityState (cyclicSector (partitionHighestTensor μ hμ)) :=
  DensityState.pure ⟨partitionHighestTensor μ hμ, highest_mem_cyclicSector _⟩
    (partitionHighestTensor_norm μ hμ)

/-- The concrete sector channel, including the invariant maximally mixed
sector replacement on inadmissible partition pairs. -/
def partitionTransitionChannel {d : ℕ} (μ ν : Fin d → ℕ)
    (hμ : Antitone μ) (hν : Antitone ν) :
    QuantumChannel (cyclicSector (partitionHighestTensor μ hμ))
      (cyclicSector (partitionHighestTensor ν hν)) := by
  by_cases h : PartitionCompatible μ ν
  · have he : (fun i ↦ μ i + (ν i - μ i)) = ν :=
      funext fun i ↦ Nat.add_sub_of_le (h.1 i)
    let a : {v : Fin d → ℕ // Antitone v} :=
      ⟨fun i ↦ μ i + (ν i - μ i), sumPartition_antitone μ (fun i ↦ ν i - μ i) hμ h.2⟩
    let b : {v : Fin d → ℕ // Antitone v} := ⟨ν, hν⟩
    have hab : a = b := Subtype.ext he
    exact Eq.mp (congrArg (fun η : {v : Fin d → ℕ // Antitone v} ↦
      QuantumChannel (cyclicSector (partitionHighestTensor μ hμ))
        (cyclicSector (partitionHighestTensor η.val η.property))) hab)
      (physicalCartanChannel μ (fun i ↦ ν i - μ i) hμ h.2)
  · exact QuantumChannel.ofContraction 0 (by intro x; simp) (partitionInvariantState ν hν)

/-- Each target copy is the actual physical canonical sector embedding. -/
def copyTransition (n m d : ℕ) (i : SchurCopy n d) (j : SchurCopy m d) :
    QuantumChannel ((recursivePhysicalDecomposition n d).get i).CanonicalSector
      (TensorRegister m (Fin d)) :=
  let A := (recursivePhysicalDecomposition n d).get i
  let B := (recursivePhysicalDecomposition m d).get j
  (QuantumChannel.ofIsometry B.canonicalEmbedding).comp
    (partitionTransitionChannel A.weight B.weight A.weight_antitone B.weight_antitone)

/-- A literal state-independent all-input quantum channel for every normalized
finite row of output-copy probabilities. -/
def channel (n m d : ℕ) (q : SchurCopy n d → SchurCopy m d → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ i, ∑ j, q i j = 1) :
    QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)) :=
  QuantumChannel.ofHilbertSum
    (fun i : SchurCopy n d ↦ ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding)
    (canonicalSectorHilbertSum (recursivePhysicalDecomposition n d)
      (recursivePhysicalDecomposition_is_decomposition n d).1
      (recursivePhysicalDecomposition_is_decomposition n d).2)
    (fun i ↦ QuantumChannel.finiteMixture (q i) (hq i) (hs i) (copyTransition n m d i))

/-- Exact full-register action, valid for all complex inputs. -/
theorem channel_apply (n m d : ℕ) (q : SchurCopy n d → SchurCopy m d → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ i, ∑ j, q i j = 1)
    (A : TraceClass (TensorRegister n (Fin d))) :
    (channel n m d q hq hs).toLinearMap A =
      ∑ i : SchurCopy n d, ∑ j : SchurCopy m d,
        (q i j : ℂ) • (copyTransition n m d i j).toLinearMap
          (conjugationLinearMap
            ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap.adjoint A) := by
  simp [channel]

/-- Exact output-copy sampling probabilities for a known spectrum. Each
physical copy has its actual sector trace as its sampling probability. -/
def knownCopyWeight (m d : ℕ) (p : Fin d → ℝ) (j : SchurCopy m d) : ℝ :=
  ((recursivePhysicalDecomposition m d).get j).character p

theorem knownCopyWeight_nonneg (m d : ℕ) (p : Fin d → ℝ) (j : SchurCopy m d) :
    0 ≤ knownCopyWeight m d p j := PhysicalHighestTensor.character_nonneg _ _

theorem knownCopyWeight_sum (m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    ∑ j : SchurCopy m d, knownCopyWeight m d p j = 1 := by
  have h := sum_physical_characters (recursivePhysicalDecomposition m d)
    (recursivePhysicalDecomposition_is_decomposition m d).1
    (recursivePhysicalDecomposition_is_decomposition m d).2 p hp
  simpa only [knownCopyWeight, hs, one_pow] using h

/-- Actual known-spectrum global cloning protocol. No unknown eigenbasis
appears in its definition. -/
def knownSpectrumChannel (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)) :=
  channel n m d (fun _ ↦ knownCopyWeight m d p)
    (fun _ ↦ knownCopyWeight_nonneg m d p) (fun _ ↦ knownCopyWeight_sum m d p hp hs)

end Cloning.TensorCloning
