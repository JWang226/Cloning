import Cloning.PCTGlobalWerner
import Cloning.PCTRankGlobalMatrixBridge

/-! The literal physical Werner sandwich for rectangular purifications.
The particle space is A × B; neither equal dimensions nor full Schmidt rank
in the physical A register is required. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.InfiniteFiniteCorner
open Cloning.GeneralSymmetricOccupation Cloning.PCTPurificationChannel
namespace Cloning.PCTRankGlobal
open Cloning.PCTGlobal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
local instance registerFiniteDimensionalRankWerner (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]

theorem physicalEmbedding_conjugation_matrix {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×B))) (L : ℕ)
    (X : Matrix (Occupation L (s+1)) (Occupation L (s+1)) ℂ) :
    operatorConjugation (physicalEmbedding u L).toContinuousLinearMap (registerLiftCLM X).1 =
      operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap
        (ofMatrix (@column L (s+1)) X) := by
  have he : conjugationLinearMap (isometry L (s+1)).toContinuousLinearMap (registerLiftCLM X) =
      matrixLift (@column L (s+1)) X := by
    rw [conjugation_registerLiftCLM]
    congr 1
    funext q
    exact isometry_single L (s+1) q
  change operatorConjugation ((tensorFrame u.orthonormal L).toContinuousLinearMap.comp
    (isometry L (s+1)).toContinuousLinearMap) (registerLiftCLM X).1 = _
  rw [← operatorConjugation_comp]
  exact congrArg (operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap)
    (congrArg Subtype.val he)

/-- Full-identity slot insertion in the fixed physical coordinates agrees with
computational tensor insertion on every occupation matrix. -/
theorem physicalPairMatrix_slotInsertion {s : ℕ} (e : Fin (s+1) ≃ A×B) (n r : ℕ)
    (X : Matrix (Occupation n (s+1)) (Occupation n (s+1)) ℂ) :
    physicalPairMatrix e n r (registerLiftCLM (slotInsertion n r
      (matrixOf (registerBasis _) (operatorConjugation
        (groupedEmbedding (coordinateFrame e) n).toContinuousLinearMap (registerLiftCLM X).1)))).1 =
      (columnMatrix n (s+1) * X * (columnMatrix n (s+1)).conjTranspose) ⊗ₖ
        (1 : Matrix (Word r (s+1)) (Word r (s+1)) ℂ) := by
  ext a b
  rw [physicalPairMatrix, registerLiftCLM_coefficient]
  simp only [slotInsertion, coordinatePairWords, coordinateWords, Equiv.trans_apply,
    Equiv.coe_fn_mk, wordPairEquiv, Fin.append_left, Fin.append_right]
  change matrixOf (registerBasis _) (operatorConjugation
      (groupedEmbedding (coordinateFrame e) n).toContinuousLinearMap (registerLiftCLM X).1)
      (pairWordsEquiv n (fun i => e (a.1 i))) (pairWordsEquiv n (fun i => e (b.1 i))) *
      (∏ j : Fin r, if e (a.2 j) = e (b.2 j) then (1:ℂ) else 0) = _
  rw [matrixOf_groupedEmbedding, physicalEmbedding_conjugation_matrix]
  simp only [matrixOf, registerBasis_apply, register_inner_single,
    coordinate_operator_coefficient, Equiv.symm_apply_apply, column_operator_coefficient,
    e.injective.eq_iff]
  congr 1
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  congr 1
  exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- The actual sector CPTP channel has the literal physical symmetric
sandwich on every complex occupation input, in one fixed computational frame. -/
theorem sectorChannel_physical_sandwich {s : ℕ} (e : Fin (s+1) ≃ A×B) (n r : ℕ)
    (X : Matrix (Occupation n (s+1)) (Occupation n (s+1)) ℂ) :
    conjugationLinearMap (physicalEmbedding (coordinateFrame e) (n+r)).toContinuousLinearMap
      ((sectorChannel n r s).toLinearMap (registerLiftCLM X)) =
    ((((n+s).choose s : ℝ) / ((n+r+s).choose s : ℝ) : ℝ) : ℂ) •
      conjugationLinearMap (physicalProjector (C:=A×B) (n+r))
        (registerLiftCLM (slotInsertion n r (matrixOf (registerBasis _)
          (operatorConjugation (groupedEmbedding (coordinateFrame e) n).toContinuousLinearMap
            (registerLiftCLM X).1)))) := by
  rw [sectorChannel_apply]
  apply Subtype.ext
  change operatorConjugation (physicalEmbedding (coordinateFrame e) (n+r)).toContinuousLinearMap
      (registerLiftCLM ((wernerChannel n r s).toFun X)).1 = _
  rw [physicalEmbedding_conjugation_matrix]
  have hp : (physicalProjector (C:=A×B) (n+r)).adjoint = physicalProjector (n+r) :=
    (isStarProjection_starProjection (U:=physicalSymmetric (C:=A×B) (n+r))).isSelfAdjoint.adjoint_eq
  have hc (T : Register (Fin (n+r) → A×B) →L[ℂ] Register (Fin (n+r) → A×B)) :
      operatorConjugation (physicalProjector (C:=A×B) (n+r)) T =
        physicalProjector (n+r) * T * physicalProjector (n+r) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [operatorConjugation_apply, hp, ContinuousLinearMap.mul_apply]
  change _ = ((((n+s).choose s : ℝ) / ((n+r+s).choose s : ℝ) : ℝ) : ℂ) •
    operatorConjugation (physicalProjector (C:=A×B) (n+r)) _
  rw [hc]
  apply physicalPairMatrix_injective e n r
  rw [physicalPairMatrix_frame, pairOperatorMatrix_ofMatrix,
    physicalPairMatrix_smul, physicalPairMatrix_mul, physicalPairMatrix_mul,
    physicalPairMatrix_projector, physicalPairMatrix_slotInsertion]
  simpa only [Complex.coe_smul] using wernerChannel_physical_sandwich n r s X

end Cloning.PCTRankGlobal
