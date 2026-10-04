import Cloning.TensorFlatProjectorGibbs
import Cloning.TensorCloningAchievabilityMixture

/-! All-input physical cloning channels driven by an exact coupling of Schur copies. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ComplexOrder Matrix
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
variable {n m d : ℕ}

def copySectorPositive (H : PhysicalHighestTensor n d)
    (U : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    PositiveTraceClass H.CanonicalSector :=
  ⟨canonicalRotatedGibbs H U p, canonicalRotatedGibbs_nonneg_of_nonneg H U p hp⟩

def coupledCopyRow (p : Fin d → ℝ) (J : SchurCopy n d → SchurCopy m d → ℝ)
    (i : SchurCopy n d) (j : SchurCopy m d) : ℝ :=
  if 0 < knownCopyWeight n d p i then J i j / knownCopyWeight n d p i else knownCopyWeight m d p j

theorem coupledCopyRow_nonneg (p : Fin d → ℝ) (J : SchurCopy n d → SchurCopy m d → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (i : SchurCopy n d) (j : SchurCopy m d) :
    0 ≤ coupledCopyRow p J i j := by
  unfold coupledCopyRow
  split_ifs with hi
  · exact div_nonneg (hJ i j) hi.le
  · exact knownCopyWeight_nonneg _ _ _ _

theorem coupledCopyRow_sum (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑a,p a=1)
    (J : SchurCopy n d → SchurCopy m d → ℝ)
    (hrow : ∀ i, ∑ j, J i j = knownCopyWeight n d p i) (i : SchurCopy n d) :
    ∑ j, coupledCopyRow p J i j = 1 := by
  by_cases hi : 0 < knownCopyWeight n d p i
  · simp only [coupledCopyRow, if_pos hi, ← Finset.sum_div, hrow,
      div_self hi.ne']
  · simp only [coupledCopyRow, if_neg hi]
    exact knownCopyWeight_sum m d p hp hs

theorem coupledCopyRow_weight (p : Fin d → ℝ) (J : SchurCopy n d → SchurCopy m d → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hrow : ∀ i, ∑ j, J i j = knownCopyWeight n d p i)
    (i : SchurCopy n d) (j : SchurCopy m d) :
    knownCopyWeight n d p i * coupledCopyRow p J i j = J i j := by
  by_cases hi : 0 < knownCopyWeight n d p i
  · simp only [coupledCopyRow, if_pos hi]
    exact mul_div_cancel₀ _ hi.ne'
  · have hz : knownCopyWeight n d p i=0 := le_antisymm (not_lt.mp hi) (knownCopyWeight_nonneg _ _ _ _)
    have hj := Finset.single_le_sum (fun j _ => hJ i j) (Finset.mem_univ j)
    rw [hrow, hz] at hj
    have hzero : J i j=0 := le_antisymm hj (hJ i j)
    simp [hz,hzero]

/-- This is a concrete state-independent CPTP map even on zero-probability input copies. -/
def coupledCopyChannel (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑a,p a=1)
    (J : SchurCopy n d → SchurCopy m d → ℝ) (hJ : ∀ i j, 0 ≤ J i j)
    (hrow : ∀ i, ∑ j, J i j = knownCopyWeight n d p i) :
    QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)) :=
  channel n m d (coupledCopyRow p J) (coupledCopyRow_nonneg p J hJ) (coupledCopyRow_sum p hp hs J hrow)

/-- Exact output mixture for the constructed channel at arbitrary nonnegative spectra. -/
theorem coupledCopyChannel_rotated_apply (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑a,p a=1)
    (J : SchurCopy n d → SchurCopy m d → ℝ) (hJ : ∀ i j, 0 ≤ J i j)
    (hrow : ∀ i, ∑ j, J i j = knownCopyWeight n d p i)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (coupledCopyChannel p hp hs J hJ hrow).toLinearMap
      (matrixTensorPower (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) n) =
      ∑ ij : SchurCopy n d × SchurCopy m d, (J ij.1 ij.2 : ℂ) •
        (copyTransition n m d ij.1 ij.2).toLinearMap
          (canonicalRotatedGibbs ((recursivePhysicalDecomposition n d).get ij.1) U p) := by
  rw [coupledCopyChannel, channel_apply]
  simp only [matrixTensorPower_canonical_block, canonicalTensorWeight_rotated_diagonal_nonneg,
    map_smul, Fintype.sum_prod_type, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← Complex.ofReal_mul, mul_comm]
  exact congrArg Complex.ofReal (coupledCopyRow_weight p J hJ hrow i j)

theorem rotatedTensor_eq_coupledCopy_mixture (p : Fin d → ℝ)
    (J : SchurCopy n d → SchurCopy m d → ℝ)
    (hcol : ∀ j, ∑ i, J i j = knownCopyWeight m d p j)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    matrixTensorPower (U * Matrix.diagonal (fun a => (p a : ℂ)) * Uᴴ) m =
      ∑ ij : SchurCopy n d × SchurCopy m d, (J ij.1 ij.2 : ℂ) •
        conjugationLinearMap ((recursivePhysicalDecomposition m d).get ij.2).canonicalEmbedding.toContinuousLinearMap
          (canonicalRotatedGibbs ((recursivePhysicalDecomposition m d).get ij.2) U p) := by
  rw [matrixTensorPower_rotated_eq_copy_mixture_nonneg]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Prod.fst,Prod.snd]
  have hh := Finset.sum_smul (R := ℂ) (f := fun i : SchurCopy n d => (J i j : ℂ))
    (s := Finset.univ) (x := conjugationLinearMap
      ((recursivePhysicalDecomposition m d).get j).canonicalEmbedding.toContinuousLinearMap
      (canonicalRotatedGibbs ((recursivePhysicalDecomposition m d).get j) U p))
  rw [← Complex.ofReal_sum, hcol] at hh
  exact hh

/-- Conditional physical transition fidelity, including zero-mass copies. -/
def nonnegativeTransitionFidelity (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (i : SchurCopy n d) (j : SchurCopy m d) : ℝ :=
  let A := (recursivePhysicalDecomposition n d).get i
  let B := (recursivePhysicalDecomposition m d).get j
  ((copySectorPositive A U p hp).map
    (partitionTransitionChannel A.weight B.weight A.weight_antitone B.weight_antitone).toPositiveTracePreservingMap).rootFidelity
    (copySectorPositive B U p hp)

/-- Joint concavity gives a genuine finite lower bound for this actual full-register channel. -/
theorem coupledCopyChannel_payoff_lower [NeZero d]
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑a,p a=1)
    (J : SchurCopy n d → SchurCopy m d → ℝ) (hJ : ∀ i j, 0 ≤ J i j)
    (hrow : ∀ i, ∑ j, J i j = knownCopyWeight n d p i)
    (hcol : ∀ j, ∑ i, J i j = knownCopyWeight m d p j)
    (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (∑ ij : SchurCopy n d × SchurCopy m d, J ij.1 ij.2 * nonnegativeTransitionFidelity p hp U ij.1 ij.2) ≤
      statePayoff n m (coupledCopyChannel p hp hs J hJ hrow)
        (conjugatedState (diagonalState p hp hs) U) := by
  let A (ij : SchurCopy n d × SchurCopy m d) :=
    (copySectorPositive ((recursivePhysicalDecomposition n d).get ij.1) U p hp).map
      (copyTransition n m d ij.1 ij.2).toPositiveTracePreservingMap
  let B (ij : SchurCopy n d × SchurCopy m d) :=
    (copySectorPositive ((recursivePhysicalDecomposition m d).get ij.2) U p hp).map
      (QuantumChannel.ofIsometry ((recursivePhysicalDecomposition m d).get ij.2).canonicalEmbedding).toPositiveTracePreservingMap
  have hmono (ij : SchurCopy n d × SchurCopy m d) :
      nonnegativeTransitionFidelity p hp U ij.1 ij.2 ≤ (A ij).rootFidelity (B ij) := by
    let C := (recursivePhysicalDecomposition n d).get ij.1
    let D := (recursivePhysicalDecomposition m d).get ij.2
    let S := (copySectorPositive C U p hp).map
      (partitionTransitionChannel C.weight D.weight C.weight_antitone D.weight_antitone).toPositiveTracePreservingMap
    let T := copySectorPositive D U p hp
    exact InfiniteFidelity.fidelity_data_processing (QuantumChannel.ofIsometry D.canonicalEmbedding) S.1 T.1 S.2 T.2
  have hconc := PositiveTraceClass.finiteMixture_rootFidelity_lower_same
    (fun ij => J ij.1 ij.2) (fun ij => hJ ij.1 ij.2) A B
  have hA : (PositiveTraceClass.finiteMixture (fun ij => J ij.1 ij.2) (fun ij => hJ ij.1 ij.2) A).1 =
      (coupledCopyChannel p hp hs J hJ hrow).toLinearMap
        (tensorState (conjugatedState (diagonalState p hp hs) U) n).1 := by
    symm
    exact coupledCopyChannel_rotated_apply p hp hs J hJ hrow U
  have hB : (PositiveTraceClass.finiteMixture (fun ij => J ij.1 ij.2) (fun ij => hJ ij.1 ij.2) B).1 =
      (tensorState (conjugatedState (diagonalState p hp hs) U) m).1 := by
    symm
    exact rotatedTensor_eq_coupledCopy_mixture p J hcol U
  have hA' : PositiveTraceClass.finiteMixture (fun ij => J ij.1 ij.2) (fun ij => hJ ij.1 ij.2) A =
      (tensorState (conjugatedState (diagonalState p hp hs) U) n).map
        (coupledCopyChannel p hp hs J hJ hrow).toPositiveTracePreservingMap := Subtype.ext hA
  have hB' : PositiveTraceClass.finiteMixture (fun ij => J ij.1 ij.2) (fun ij => hJ ij.1 ij.2) B =
      tensorState (conjugatedState (diagonalState p hp hs) U) m := Subtype.ext hB
  rw [hA',hB'] at hconc
  exact (Finset.sum_le_sum (fun ij _ => mul_le_mul_of_nonneg_left (hmono ij) (hJ ij.1 ij.2))).trans hconc

end Cloning.TensorCloning
