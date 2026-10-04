import Cloning.TensorCloningBlockFidelity
import Cloning.InfiniteFidelityMixtureRestriction

/-! Exact finite error bound for the full physical channel after retaining
chosen Schur-copy transitions. Normalized retained outputs are constructed. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass
open Cloning.Hybrid Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.InfiniteFidelityHilbertSum
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
local instance {n d : ℕ} (H : PhysicalHighestTensor n d) : CompleteSpace H.CanonicalSector :=
  inferInstance

def retainedCopyWeight (n m d : ℕ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (keep : SchurCopy n d → SchurCopy m d → Prop) (i : SchurCopy n d) (j : SchurCopy m d) : ℝ :=
  PositiveTraceClass.maskedWeight (fun a ↦ w a j) (fun a ↦ keep a j) i

theorem retainedCopyWeight_nonneg (n m d : ℕ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (keep : SchurCopy n d → SchurCopy m d → Prop) :
    ∀ i j, 0 ≤ retainedCopyWeight n m d w keep i j :=
  fun i j ↦ PositiveTraceClass.maskedWeight_nonneg _ (fun a ↦ hw a j) _ i

def normalizedCopyBlock (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (w : SchurCopy n d → SchurCopy m d → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (keep : SchurCopy n d → SchurCopy m d → Prop)
    (j : SchurCopy m d) : PositiveTraceClass ((recursivePhysicalDecomposition m d).get j).CanonicalSector :=
  PositiveTraceClass.normalized
    (copyOutputBlock n m d p hp U (retainedCopyWeight n m d w keep)
      (retainedCopyWeight_nonneg n m d w hw keep) j)
    (copySectorState ((recursivePhysicalDecomposition m d).get j) U p hp)

theorem normalizedCopyBlock_eq_mixture (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (w : SchurCopy n d → SchurCopy m d → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (keep : SchurCopy n d → SchurCopy m d → Prop) (j : SchurCopy m d)
    (hr : 0 < ∑ i : {i // keep i j}, w i.val j) :
    normalizedCopyBlock n m d p hp U w hw keep j =
      PositiveTraceClass.finiteMixture
        (fun i : {i // keep i j} ↦ w i.val j / ∑ a : {i // keep i j}, w a.val j)
        (fun i ↦ div_nonneg (hw i.val j) hr.le)
        (fun i ↦ copyTransitionState n m d p hp U i.val j) := by
  exact PositiveTraceClass.normalized_masked_mixture_eq (fun i ↦ w i j) (fun i ↦ hw i j)
    (fun i ↦ keep i j) (fun i ↦ copyTransitionState n m d p hp U i j)
    (fun i ↦ copyTransitionState_norm n m d p hp U hU i j) _ hr

theorem copyBlocks_factorization_bound {d : ℕ} (n m : ℕ)
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (w : SchurCopy n (d+1) → SchurCopy m (d+1) → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hs : ∑ j, ∑ i, w i j ≤ 1) (keep : SchurCopy n (d+1) → SchurCopy m (d+1) → Prop)
    (c η : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ j, 0 < ∑ i, retainedCopyWeight n m (d+1) w keep i j →
      |(normalizedCopyBlock n m (d+1) p.eigenvalue p.positive U w hw keep j).rootFidelity
        (copySectorState ((recursivePhysicalDecomposition m (d+1)).get j) U p.eigenvalue p.positive)-c| ≤ η) :
    |(orthogonalSum (fun j : SchurCopy m (d+1) ↦ ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding)
        (copyOutputBlock n m (d+1) p.eigenvalue p.positive U w hw)).rootFidelity
      (orthogonalSum (fun j : SchurCopy m (d+1) ↦ ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding)
        (fun j ↦ PositiveTraceClass.scale ⟨knownCopyWeight m (d+1) p.eigenvalue j, knownCopyWeight_nonneg _ _ _ _⟩
          (copySectorState ((recursivePhysicalDecomposition m (d+1)).get j) U p.eigenvalue p.positive))) -
      c * Cloning.BlockFidelity.classicalAffinity (fun j ↦ ∑ i, w i j) (knownCopyWeight m (d+1) p.eigenvalue)| ≤
      η + 2 * Real.sqrt (∑ j, ∑ i, if keep i j then 0 else w i j) := by
  let V (j : SchurCopy m (d+1)) := ((recursivePhysicalDecomposition m (d+1)).get j).canonicalEmbedding
  let X := copyOutputBlock n m (d+1) p.eigenvalue p.positive U w hw
  let G := copyOutputBlock n m (d+1) p.eigenvalue p.positive U
    (retainedCopyWeight n m (d+1) w keep) (retainedCopyWeight_nonneg n m (d+1) w hw keep)
  let B (j : SchurCopy m (d+1)) := copySectorState ((recursivePhysicalDecomposition m (d+1)).get j)
    U p.eigenvalue p.positive
  let C := normalizedCopyBlock n m (d+1) p.eigenvalue p.positive U w hw keep
  let r (j : SchurCopy m (d+1)) := ∑ i, retainedCopyWeight n m (d+1) w keep i j
  have hr j : 0 ≤ r j := Finset.sum_nonneg (fun i _ ↦ retainedCopyWeight_nonneg _ _ _ w hw keep i j)
  have hUn : (U.val)ᴴ*U.val=1 := Unitary.star_mul_self_of_mem U.property
  have hB j : ‖(B j).1‖ = 1 := canonicalRotatedGibbs_norm
    ((recursivePhysicalDecomposition m (d+1)).get j) U hUn p.eigenvalue p.positive
  have hC j : ‖(C j).1‖ = 1 := PositiveTraceClass.norm_normalized (G j) (B j) (hB j)
  have hG j : ‖(G j).1‖ = r j := copyOutputBlock_norm n m (d+1) p.eigenvalue p.positive U hUn
    (retainedCopyWeight n m (d+1) w keep) (retainedCopyWeight_nonneg n m (d+1) w hw keep) j
  have hX j : ‖(X j).1‖ = ∑ i, w i j := copyOutputBlock_norm n m (d+1) p.eigenvalue p.positive U hUn w hw j
  have he j : PositiveTraceClass.scale ⟨r j,hr j⟩ (C j) = G j := by
    have h := PositiveTraceClass.scale_normalized (G j) (B j)
    simpa only [hG] using h
  have hle j : (G j).1.1 ≤ (X j).1.1 := by
    exact PositiveTraceClass.finiteMixture_mono_weights
      (fun i ↦ retainedCopyWeight n m (d+1) w keep i j) (fun i ↦ w i j)
      (fun i ↦ retainedCopyWeight_nonneg n m (d+1) w hw keep i j) (fun i ↦ hw i j)
      (by
        intro i
        dsimp only [retainedCopyWeight, PositiveTraceClass.maskedWeight]
        split_ifs
        · exact le_rfl
        · exact hw i j)
      (fun i ↦ copyTransitionState n m (d+1) p.eigenvalue p.positive U i j)
  have hscale j : (PositiveTraceClass.scale ⟨r j,hr j⟩ (C j)).1.1 ≤ (X j).1.1 := by
    have ho := congrArg (fun Z : PositiveTraceClass
      ((recursivePhysicalDecomposition m (d+1)).get j).CanonicalSector ↦ Z.1.1) (he j)
    exact ho.le.trans (hle j)
  have hXs : (∑ j, ‖(X j).1‖) ≤ 1 := by
    calc
      _ = ∑ j, ∑ i, w i j := Finset.sum_congr rfl (fun j _ ↦ hX j)
      _ ≤ 1 := hs
  have hf := orthogonalSum_factorization_bound V
    (canonicalSectorFamily_orthogonal (recursivePhysicalDecomposition m (d+1))
      (recursivePhysicalDecomposition_is_decomposition m (d+1)).1)
    (fun j ↦ partitionBasis ((recursivePhysicalDecomposition m (d+1)).get j).weight
      ((recursivePhysicalDecomposition m (d+1)).get j).weight_antitone)
    X C B (knownCopyWeight m (d+1) p.eigenvalue) r (knownCopyWeight_nonneg m (d+1) p.eigenvalue) hr
    (knownCopyWeight_sum m (d+1) p.eigenvalue (fun a ↦ (p.positive a).le) p.normalized)
    hXs hC hB hscale
    c η hc0 hc1 hη hsector
  have hδ : (∑ j, (‖(X j).1‖-r j)) = ∑ j, ∑ i, if keep i j then 0 else w i j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hX]
    dsimp only [r]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [retainedCopyWeight, PositiveTraceClass.maskedWeight]
    split_ifs <;> simp
  rw [hδ] at hf
  simpa only [hX] using hf

end Cloning.TensorCloning
