import Cloning.PCTRankGlobalChannels

/-! Rectangular symmetric-sector channels for a smaller purification environment. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner
open Cloning.PCTGlobal (operatorConjugation_comp)
namespace Cloning.PCTRankGlobal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]
local instance registerFiniteDimensionalBridge (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The physical occupation embedding resolves the full symmetric projection. -/
theorem physicalEmbedding_projection {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B))) (n : ℕ) :
    (physicalEmbedding u n).toContinuousLinearMap.comp
      (physicalEmbedding u n).toContinuousLinearMap.adjoint = physicalProjector n := by
  apply ContinuousLinearMap.ext
  intro y
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← physicalEmbedding_range u n]
    exact ⟨_,rfl⟩
  · intro w hw
    rw [← physicalEmbedding_range u n] at hw
    obtain ⟨x,rfl⟩ := hw
    rw [inner_sub_left]
    change ⟪y, physicalEmbedding u n x⟫_ℂ -
      ⟪physicalEmbedding u n ((physicalEmbedding u n).toContinuousLinearMap.adjoint y),
        physicalEmbedding u n x⟫_ℂ = 0
    rw [LinearIsometry.inner_map_map, ContinuousLinearMap.adjoint_inner_left]
    exact sub_self _

theorem regroup_single (n : ℕ) (a : Fin n → A × B) :
    regroup n (lp.single 2 a 1) = lp.single 2 (pairWordsEquiv n a) 1 := by
  rw [regroup, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

/-- Regrouping preserves every computational coefficient under its literal
word equivalence, for arbitrary operators. -/
theorem matrixOf_regroup (n : ℕ)
    (T : Register (Fin n → A × B) →L[ℂ] Register (Fin n → A × B))
    (a c : Fin n → A × B) :
    matrixOf (registerBasis _) (operatorConjugation (regroup n).toContinuousLinearMap T)
      (pairWordsEquiv n a) (pairWordsEquiv n c) =
      matrixOf (registerBasis _) T a c := by
  simp only [matrixOf, registerBasis_apply, operatorConjugation_apply]
  rw [← regroup_single n a, ← regroup_single n c, isometry_adjoint_apply_self]
  exact (regroup n).inner_map_map _ _

/-- Exact matrix-coordinate relation between grouped and physical occupation
embeddings, valid for all complex input matrices. -/
theorem matrixOf_groupedEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B))) (n : ℕ)
    (X : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ)
    (a c : Fin n → A × B) :
    matrixOf (registerBasis _)
      (operatorConjugation (groupedEmbedding u n).toContinuousLinearMap (registerLiftCLM X).1)
      (pairWordsEquiv n a) (pairWordsEquiv n c) =
    matrixOf (registerBasis _)
      (operatorConjugation (physicalEmbedding u n).toContinuousLinearMap (registerLiftCLM X).1)
      a c := by
  change matrixOf (registerBasis _)
    (operatorConjugation ((regroup n).toContinuousLinearMap.comp
      (physicalEmbedding u n).toContinuousLinearMap) (registerLiftCLM X).1) _ _ = _
  rw [← operatorConjugation_comp]
  exact matrixOf_regroup n _ a c

/-- Identity-ancilla insertion from the grouped purification input into the
first `n` physical slots. -/
def slotInsertion (n r : ℕ)
    (X : Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ) :
    Matrix (Fin (n + r) → A × B) (Fin (n + r) → A × B) ℂ :=
  fun a c => X
    ((fun i => (a (Fin.castAdd r i)).1), (fun i => (a (Fin.castAdd r i)).2))
    ((fun i => (c (Fin.castAdd r i)).1), (fun i => (c (Fin.castAdd r i)).2)) *
    ∏ j : Fin r, if a (Fin.natAdd n j) = c (Fin.natAdd n j) then 1 else 0

def slotInsertionCLM (n r : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ →L[ℂ]
      Matrix (Fin (n + r) → A × B) (Fin (n + r) → A × B) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := slotInsertion n r
      map_add' := by intros; ext a c; simp [slotInsertion, add_mul]
      map_smul' := by intros; ext a c; simp [slotInsertion, mul_assoc] }


end Cloning.PCTRankGlobal
