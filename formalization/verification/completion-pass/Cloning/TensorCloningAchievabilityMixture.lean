import Cloning.TensorCloningChannel
import Cloning.TensorCloningPayoff
import Cloning.TensorLANEmbeddingSchurState
import Cloning.InfiniteFidelityFiniteMixture

/-! A finite physical lower bound for the concrete known-spectrum cloner.
The joint weights are the literal source and target Schur-copy probabilities;
joint concavity compares its actual output with the actual target tensor. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.Hybrid Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The actual normalized state of an individual physical Schur copy. -/
def copySectorState {n d : ℕ} (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    PositiveTraceClass H.CanonicalSector :=
  ⟨canonicalRotatedGibbs H U p, canonicalRotatedGibbs_nonneg H U p hp⟩

def jointCopyWeight (n m d : ℕ) (p : Fin d → ℝ)
    (ij : SchurCopy n d × SchurCopy m d) : ℝ :=
  knownCopyWeight n d p ij.1 * knownCopyWeight m d p ij.2

theorem jointCopyWeight_nonneg (n m d : ℕ) (p : Fin d → ℝ)
    (ij : SchurCopy n d × SchurCopy m d) : 0 ≤ jointCopyWeight n m d p ij :=
  mul_nonneg (knownCopyWeight_nonneg n d p ij.1) (knownCopyWeight_nonneg m d p ij.2)

theorem jointCopyWeight_sum (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    ∑ ij, jointCopyWeight n m d p ij = 1 := by
  simp only [jointCopyWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    knownCopyWeight_sum m d p hp hs, mul_one, knownCopyWeight_sum n d p hp hs]

def transitionFidelity (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (i : SchurCopy n d) (j : SchurCopy m d) : ℝ :=
  let A := (recursivePhysicalDecomposition n d).get i
  let B := (recursivePhysicalDecomposition m d).get j
  ((copySectorState A U p hp).map
    (partitionTransitionChannel A.weight B.weight A.weight_antitone B.weight_antitone).toPositiveTracePreservingMap).rootFidelity
    (copySectorState B U p hp)

theorem transitionFidelity_nonneg (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (i : SchurCopy n d) (j : SchurCopy m d) :
    0 ≤ transitionFidelity n m d p hp U i j := PositiveTraceClass.rootFidelity_nonneg _ _

/-- Exact joint-mixture output of the concrete physical cloner. -/
theorem knownSpectrumChannel_rotated_apply (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hs : ∑ a, p a = 1) (U : Matrix (Fin d) (Fin d) ℂ) :
    (knownSpectrumChannel n m d p (fun a => (hp a).le) hs).toLinearMap
      (matrixTensorPower (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) n) =
      ∑ ij : SchurCopy n d × SchurCopy m d,
        (jointCopyWeight n m d p ij : ℂ) •
          (copyTransition n m d ij.1 ij.2).toLinearMap
            (canonicalRotatedGibbs ((recursivePhysicalDecomposition n d).get ij.1) U p) := by
  rw [knownSpectrumChannel, channel_apply]
  simp only [matrixTensorPower_canonical_block, canonicalTensorWeight_rotated_diagonal _ U p hp,
    map_smul, Fintype.sum_prod_type, jointCopyWeight, Complex.ofReal_mul, mul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- Jointly repeat the actual target copy mixture over the source-copy law. -/
theorem rotatedTensor_eq_jointCopy_mixture (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hs : ∑ a, p a = 1) (U : Matrix (Fin d) (Fin d) ℂ) :
    matrixTensorPower (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) m =
      ∑ ij : SchurCopy n d × SchurCopy m d,
        (jointCopyWeight n m d p ij : ℂ) •
          conjugationLinearMap ((recursivePhysicalDecomposition m d).get ij.2).canonicalEmbedding.toContinuousLinearMap
            (canonicalRotatedGibbs ((recursivePhysicalDecomposition m d).get ij.2) U p) := by
  rw [matrixTensorPower_rotated_eq_copy_mixture U p hp]
  simp only [jointCopyWeight, Fintype.sum_prod_type, Complex.ofReal_mul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let X := conjugationLinearMap ((recursivePhysicalDecomposition m d).get j).canonicalEmbedding.toContinuousLinearMap
    (canonicalRotatedGibbs ((recursivePhysicalDecomposition m d).get j) U p)
  have hh := Finset.sum_smul (R := ℂ)
    (f := fun i : SchurCopy n d => (knownCopyWeight n d p i : ℂ))
    (s := Finset.univ) (x := (knownCopyWeight m d p j : ℂ) • X)
  rw [← Complex.ofReal_sum, knownCopyWeight_sum n d p (fun a => (hp a).le) hs,
    Complex.ofReal_one, one_smul] at hh
  exact hh


/-- The physical payoff dominates the average of the genuine conditional
sector fidelities. No compatibility, orthogonality or asymptotic premise is
needed for this finite inequality. -/
theorem knownSpectrumChannel_payoff_lower {d : ℕ} (n m : ℕ)
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    (∑ ij : SchurCopy n (d+1) × SchurCopy m (d+1),
      jointCopyWeight n m (d+1) p.eigenvalue ij *
        transitionFidelity n m (d+1) p.eigenvalue p.positive U ij.1 ij.2) ≤
      spectrumPayoff n m (knownSpectrumChannel n m (d+1) p.eigenvalue
        (fun a => (p.positive a).le) p.normalized) p U := by
  let A (ij : SchurCopy n (d+1) × SchurCopy m (d+1)) :=
    (copySectorState ((recursivePhysicalDecomposition n (d+1)).get ij.1) U p.eigenvalue p.positive).map
      (copyTransition n m (d+1) ij.1 ij.2).toPositiveTracePreservingMap
  let B (ij : SchurCopy n (d+1) × SchurCopy m (d+1)) :=
    (copySectorState ((recursivePhysicalDecomposition m (d+1)).get ij.2) U p.eigenvalue p.positive).map
      (QuantumChannel.ofIsometry ((recursivePhysicalDecomposition m (d+1)).get ij.2).canonicalEmbedding).toPositiveTracePreservingMap
  have hmono (ij : SchurCopy n (d+1) × SchurCopy m (d+1)) :
      transitionFidelity n m (d+1) p.eigenvalue p.positive U ij.1 ij.2 ≤
        (A ij).rootFidelity (B ij) := by
    let C := (recursivePhysicalDecomposition n (d+1)).get ij.1
    let D := (recursivePhysicalDecomposition m (d+1)).get ij.2
    let S := (copySectorState C U p.eigenvalue p.positive).map
      (partitionTransitionChannel C.weight D.weight C.weight_antitone D.weight_antitone).toPositiveTracePreservingMap
    let T := copySectorState D U p.eigenvalue p.positive
    exact InfiniteFidelity.fidelity_data_processing
      (QuantumChannel.ofIsometry D.canonicalEmbedding) S.1 T.1 S.2 T.2
  have hconc := PositiveTraceClass.finiteMixture_rootFidelity_lower_same
    (jointCopyWeight n m (d+1) p.eigenvalue) (jointCopyWeight_nonneg n m (d+1) p.eigenvalue) A B
  have hA : (PositiveTraceClass.finiteMixture (jointCopyWeight n m (d+1) p.eigenvalue)
      (jointCopyWeight_nonneg n m (d+1) p.eigenvalue) A).1 =
      (knownSpectrumChannel n m (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized).toLinearMap
        (tensorState (orbitState p U) n).1 := by
    symm
    exact knownSpectrumChannel_rotated_apply n m (d+1) p.eigenvalue p.positive p.normalized U
  have hB : (PositiveTraceClass.finiteMixture (jointCopyWeight n m (d+1) p.eigenvalue)
      (jointCopyWeight_nonneg n m (d+1) p.eigenvalue) B).1 = (tensorState (orbitState p U) m).1 := by
    symm
    exact rotatedTensor_eq_jointCopy_mixture n m (d+1) p.eigenvalue p.positive p.normalized U
  have hA' : PositiveTraceClass.finiteMixture (jointCopyWeight n m (d+1) p.eigenvalue)
      (jointCopyWeight_nonneg n m (d+1) p.eigenvalue) A =
      (tensorState (orbitState p U) n).map
        (knownSpectrumChannel n m (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized).toPositiveTracePreservingMap :=
    Subtype.ext hA
  have hB' : PositiveTraceClass.finiteMixture (jointCopyWeight n m (d+1) p.eigenvalue)
      (jointCopyWeight_nonneg n m (d+1) p.eigenvalue) B = tensorState (orbitState p U) m :=
    Subtype.ext hB
  rw [hA', hB'] at hconc
  exact (Finset.sum_le_sum (fun ij _ =>
    mul_le_mul_of_nonneg_left (hmono ij) (jointCopyWeight_nonneg n m (d+1) p.eigenvalue ij))).trans hconc

end Cloning.TensorCloning
