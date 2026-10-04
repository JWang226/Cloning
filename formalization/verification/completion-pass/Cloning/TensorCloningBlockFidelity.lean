import Cloning.TensorCloningUniversalMixture
import Cloning.InfiniteFidelityMixtureNormalization

/-! Exact orthogonal block fidelity for the actual global cloning channel.
Physical Schur copies are kept individually, so multiplicities are exact. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.Hybrid Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.InfiniteFidelityHilbertSum
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def copyTransitionState (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (i : SchurCopy n d) (j : SchurCopy m d) :
    PositiveTraceClass ((recursivePhysicalDecomposition m d).get j).CanonicalSector :=
  (copySectorState ((recursivePhysicalDecomposition n d).get i) U p hp).map
    (partitionTransitionChannel _ _
      ((recursivePhysicalDecomposition n d).get i).weight_antitone
      ((recursivePhysicalDecomposition m d).get j).weight_antitone).toPositiveTracePreservingMap

theorem copyTransitionState_norm (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U = 1)
    (i : SchurCopy n d) (j : SchurCopy m d) :
    ‖(copyTransitionState n m d p hp U i j).1‖ = 1 := by
  rw [copyTransitionState, PositiveTraceClass.norm_map]
  exact canonicalRotatedGibbs_norm _ U hU p hp

def copyOutputBlock (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (j : SchurCopy m d) :
    PositiveTraceClass ((recursivePhysicalDecomposition m d).get j).CanonicalSector :=
  PositiveTraceClass.finiteMixture (fun i ↦ w i j) (fun i ↦ hw i j)
    (fun i ↦ copyTransitionState n m d p hp U i j)

theorem copyOutputBlock_norm (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U = 1)
    (w : SchurCopy n d → SchurCopy m d → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (j : SchurCopy m d) : ‖(copyOutputBlock n m d p hp U w hw j).1‖ = ∑ i, w i j := by
  simp only [copyOutputBlock, PositiveTraceClass.norm_finiteMixture,
    copyTransitionState_norm n m d p hp U hU, mul_one]

theorem copyOutputBlock_orthogonalSum (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) :
    (orthogonalSum (fun j : SchurCopy m d ↦ ((recursivePhysicalDecomposition m d).get j).canonicalEmbedding)
      (copyOutputBlock n m d p hp U w hw)).1 =
    ∑ ij : SchurCopy n d × SchurCopy m d, (w ij.1 ij.2 : ℂ) •
      (copyTransition n m d ij.1 ij.2).toLinearMap
        (canonicalRotatedGibbs ((recursivePhysicalDecomposition n d).get ij.1) U p) := by
  rw [orthogonalSum_val]
  simp only [copyOutputBlock, PositiveTraceClass.finiteMixture_val, map_sum, map_smul,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

theorem copyTarget_orthogonalSum (m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (orthogonalSum (fun j : SchurCopy m d ↦ ((recursivePhysicalDecomposition m d).get j).canonicalEmbedding)
      (fun j ↦ PositiveTraceClass.scale ⟨knownCopyWeight m d p j, knownCopyWeight_nonneg _ _ _ _⟩
        (copySectorState ((recursivePhysicalDecomposition m d).get j) U p hp))).1 =
      matrixTensorPower (U * Matrix.diagonal (fun a ↦ (p a : ℂ)) * Uᴴ) m := by
  rw [orthogonalSum_val, matrixTensorPower_rotated_eq_copy_mixture (n := m) (d := d) U p hp]
  apply Finset.sum_congr rfl
  intro j hj
  change conjugationLinearMap ((recursivePhysicalDecomposition m d).get j).canonicalEmbedding.toContinuousLinearMap
    ((knownCopyWeight m d p j : ℂ) • canonicalRotatedGibbs ((recursivePhysicalDecomposition m d).get j) U p) = _
  rw [map_smul]
  rfl

/-- The physical payoff has exactly the fidelity of its actual orthogonal
copy blocks whenever its actual joint-mixture action is identified. -/
theorem spectrumPayoff_eq_copyBlocks {d : ℕ} (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (d+1))) (TensorRegister m (Fin (d+1))))
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (w : SchurCopy n (d+1) → SchurCopy m (d+1) → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hΦ : Φ.toLinearMap (matrixTensorPower (U.val * Matrix.diagonal (fun a ↦ (p.eigenvalue a : ℂ)) * U.valᴴ) n) =
      ∑ ij : SchurCopy n (d+1) × SchurCopy m (d+1), (w ij.1 ij.2 : ℂ) •
        (copyTransition n m (d+1) ij.1 ij.2).toLinearMap
          (canonicalRotatedGibbs ((recursivePhysicalDecomposition n (d+1)).get ij.1) U p.eigenvalue)) :
    spectrumPayoff n m Φ p U =
      (orthogonalSum (fun j : SchurCopy m (d+1) ↦ ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding)
        (copyOutputBlock n m (d+1) p.eigenvalue p.positive U w hw)).rootFidelity
      (orthogonalSum (fun j : SchurCopy m (d+1) ↦ ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding)
        (fun j ↦ PositiveTraceClass.scale ⟨knownCopyWeight m (d+1) p.eigenvalue j, knownCopyWeight_nonneg _ _ _ _⟩
          (copySectorState ((recursivePhysicalDecomposition m (d+1)).get j) U p.eigenvalue p.positive))) := by
  have hA : (tensorState (orbitState p U) n).map Φ.toPositiveTracePreservingMap =
      orthogonalSum (fun j : SchurCopy m (d+1) ↦ ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding)
        (copyOutputBlock n m (d+1) p.eigenvalue p.positive U w hw) := by
    apply Subtype.ext
    rw [copyOutputBlock_orthogonalSum]
    exact hΦ
  have hB : tensorState (orbitState p U) m =
      orthogonalSum (fun j : SchurCopy m (d+1) ↦ ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding)
        (fun j ↦ PositiveTraceClass.scale ⟨knownCopyWeight m (d+1) p.eigenvalue j, knownCopyWeight_nonneg _ _ _ _⟩
          (copySectorState ((recursivePhysicalDecomposition m (d+1)).get j) U p.eigenvalue p.positive)) := by
    apply Subtype.ext
    rw [copyTarget_orthogonalSum]
    rfl
  exact congrArg₂ PositiveTraceClass.rootFidelity hA hB

end Cloning.TensorCloning
