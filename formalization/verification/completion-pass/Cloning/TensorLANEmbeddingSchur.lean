import Cloning.TensorLANEmbeddingTotal
import Cloning.TensorSchurMultiplicityDecomposition
import Cloning.TensorSchurDecompositionIsometry
import Cloning.MixedChannelsSectorInstrument
import Cloning.MixedChannelsFiniteSelector

/-! Genuine mixed channels assembled from the exhaustive recursive physical
Schur decomposition and the concrete all-input sector/Fock channels. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass MeasureTheory Cloning.Hybrid
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

abbrev SchurCopy (n d : ℕ) := Fin (recursivePhysicalDecomposition n d).length

def copyToFock (n d R : ℕ) (i : SchurCopy n d) :
    QuantumChannel ((recursivePhysicalDecomposition n d).get i).CanonicalSector (RootFock d) :=
  let H := (recursivePhysicalDecomposition n d).get i
  sectorToFockTotal (partitionHighestTensor H.weight H.weight_antitone) H.weight R

/-- Reverse transport lands in the actual physical copy through its proved
canonical isometric embedding. -/
def fockToCopy (n d R : ℕ) (i : SchurCopy n d) :
    QuantumChannel (RootFock d) (TensorRegister n (Fin d)) :=
  let H := (recursivePhysicalDecomposition n d).get i
  (QuantumChannel.ofIsometry H.canonicalEmbedding).comp
    (fockToSectorTotal (partitionHighestTensor H.weight H.weight_antitone) H.weight R
      (partitionHighestTensor_norm H.weight H.weight_antitone))

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Measure the actual complete physical sector sum, use its sector channel,
and emit the prescribed probability density for the classical label. All
quantum and classical trace normalization is derived. -/
def schurForward (n d R : ℕ) (g : SchurCopy n d → X → ℝ)
    (hg : ∀ i, Integrable (g i) ν) (hg0 : ∀ i x, 0 ≤ g i x)
    (hprob : ∀ i, ∫ x, g i x ∂ν = 1) :
    QuantumToHybrid (TensorRegister n (Fin d)) (RootFock d) ν :=
  QuantumToHybrid.ofHilbertSum
    (fun i : SchurCopy n d => ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding)
    (canonicalSectorHilbertSum (recursivePhysicalDecomposition n d)
      (recursivePhysicalDecomposition_is_decomposition n d).1
      (recursivePhysicalDecomposition_is_decomposition n d).2)
    (copyToFock n d R) g hg hg0 hprob

theorem schurForward_apply (n d R : ℕ) (g : SchurCopy n d → X → ℝ)
    (hg : ∀ i, Integrable (g i) ν) (hg0 : ∀ i x, 0 ≤ g i x)
    (hprob : ∀ i, ∫ x, g i x ∂ν = 1) (A : TraceClass (TensorRegister n (Fin d))) :
    (schurForward n d R g hg hg0 hprob).map A =
      ∑ i : SchurCopy n d, prepareL1 (g i) (hg i)
        ((copyToFock n d R i).toLinearMap
          (conjugationLinearMap
            ((recursivePhysicalDecomposition n d).get i).canonicalEmbedding.toContinuousLinearMap.adjoint A)) :=
  QuantumToHybrid.ofHilbertSum_apply _ _ _ _ _ _ _ A

/-- The additional outcome is an explicit physical replacement state for
classical data outside the represented cell family. -/
def copyReverseWithFallback (n d R : ℕ) (ρ : DensityState (TensorRegister n (Fin d))) :
    Option (SchurCopy n d) → QuantumChannel (RootFock d) (TensorRegister n (Fin d))
  | none => QuantumChannel.ofContraction 0 (by intro x; simp) ρ
  | some i => fockToCopy n d R i

/-- Any proved classical cell selector now yields a genuine reverse mixed
channel on all hybrid inputs, with the actual physical output register. -/
def schurReverse (n d R : ℕ) (ρ : DensityState (TensorRegister n (Fin d)))
    (χ : Option (SchurCopy n d) → X → ℝ)
    (hχ : ∀ i, AEStronglyMeasurable (χ i) ν)
    (hχ0 : ∀ i x, 0 ≤ χ i x) (hχsum : ∀ x, ∑ i, χ i x = 1) :
    HybridToQuantum (RootFock d) (TensorRegister n (Fin d)) ν :=
  HybridToQuantum.finiteSelector χ hχ hχ0 hχsum (copyReverseWithFallback n d R ρ)

end Cloning.TensorLAN
