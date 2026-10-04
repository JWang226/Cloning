import Cloning.PCTGlobalRecovery

/-! Matrix, physical occupation, and grouped-register bridges for the
all-input PCT channel identity. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel
open Cloning.GeneralSymmetricOccupation Cloning.InfiniteFiniteCorner
namespace Cloning.PCTGlobal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem conjugation_rankOneOperator (V : H →L[ℂ] K) (x y : H) :
    conjugationLinearMap V (rankOneOperator x y) = rankOneOperator (V x) (V y) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro z
  change V (⟪y, V.adjoint z⟫_ℂ • x) = ⟪V y, z⟫_ℂ • V x
  rw [map_smul, ContinuousLinearMap.adjoint_inner_right]

theorem conjugation_matrixLift {I : Type*} [Fintype I] [DecidableEq I]
    (V : H →L[ℂ] K) (v : I → H) (X : Matrix I I ℂ) :
    conjugationLinearMap V (matrixLift v X) = matrixLift (fun i => V (v i)) X := by
  simp only [matrixLift, map_sum, map_smul, conjugation_rankOneOperator]

theorem conjugation_registerLiftCLM {I : Type*} [Fintype I] [DecidableEq I]
    (V : Register I →L[ℂ] K) (X : Matrix I I ℂ) :
    conjugationLinearMap V (registerLiftCLM X) =
      matrixLift (fun i => V (registerBasis I i)) X :=
  conjugation_matrixLift V (registerBasis I) X

theorem operatorConjugation_comp (V : K →L[ℂ] L) (W : H →L[ℂ] K) (T : H →L[ℂ] H) :
    operatorConjugation V (operatorConjugation W T) = operatorConjugation (V.comp W) T := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [operatorConjugation_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply]

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
local instance registerFiniteDimensionalBridge (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- The physical occupation embedding resolves the full symmetric projection. -/
theorem physicalEmbedding_projection {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ) :
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

theorem regroup_single (n : ℕ) (a : Fin n → A × A) :
    regroup n (lp.single 2 a 1) = lp.single 2 (pairWordsEquiv n a) 1 := by
  rw [regroup, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

/-- Regrouping preserves every computational coefficient under its literal
word equivalence, for arbitrary operators. -/
theorem matrixOf_regroup (n : ℕ)
    (T : Register (Fin n → A × A) →L[ℂ] Register (Fin n → A × A))
    (a c : Fin n → A × A) :
    matrixOf (registerBasis _) (operatorConjugation (regroup n).toContinuousLinearMap T)
      (pairWordsEquiv n a) (pairWordsEquiv n c) =
      matrixOf (registerBasis _) T a c := by
  simp only [matrixOf, registerBasis_apply, operatorConjugation_apply]
  rw [← regroup_single n a, ← regroup_single n c, isometry_adjoint_apply_self]
  exact (regroup n).inner_map_map _ _

/-- Exact matrix-coordinate relation between grouped and physical occupation
embeddings, valid for all complex input matrices. -/
theorem matrixOf_groupedEmbedding {s : ℕ}
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (n : ℕ)
    (X : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ)
    (a c : Fin n → A × A) :
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

end Cloning.PCTGlobal
