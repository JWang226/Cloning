import Cloning.PCTCoordinateFrame
import Cloning.PCTGlobalMatrixBridge

/-! Unrestricted computational transport of the physical Werner sandwich. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.InfiniteFiniteCorner
open Cloning.GeneralSymmetricOccupation Cloning.PCTPurificationChannel
namespace Cloning.PCTGlobal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
local instance registerFiniteDimensionalWerner (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}

def coordinateWords (e : Fin d ≃ C) (L : ℕ) : Word L d ≃ (Fin L → C) where
  toFun w := fun i => e (w i)
  invFun w := fun i => e.symm (w i)
  left_inv w := by funext i; exact e.symm_apply_apply (w i)
  right_inv w := by funext i; exact e.apply_symm_apply (w i)

def coordinatePairWords (e : Fin d ≃ C) (n r : ℕ) :
    Word n d × Word r d ≃ (Fin (n+r) → C) :=
  (wordPairEquiv n r d).trans (coordinateWords e (n+r))

def physicalPairMatrix (e : Fin d ≃ C) (n r : ℕ)
    (T : Register (Fin (n+r) → C) →L[ℂ] Register (Fin (n+r) → C)) :
    Matrix (Word n d × Word r d) (Word n d × Word r d) ℂ :=
  fun a b => T (lp.single 2 (coordinatePairWords e n r b) 1) (coordinatePairWords e n r a)

private theorem register_operator_expansion {I : Type*} [Fintype I] [DecidableEq I]
    (T : Register I →L[ℂ] Register I) (x : Register I) (a : I) :
    T x a = ∑ b, T (lp.single 2 b 1) a * x b := by
  have hx : x = ∑ b, x b • (lp.single 2 b 1 : Register I) := by
    ext b
    simp [lp.single_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum, map_smul, lp.coeFn_smul, mul_comm]

theorem physicalPairMatrix_injective (e : Fin d ≃ C) (n r : ℕ) :
    Function.Injective (physicalPairMatrix e n r) := by
  intro T S h
  apply register_operator_ext
  intro a b
  obtain ⟨u,rfl⟩ := (coordinatePairWords e n r).surjective a
  obtain ⟨v,rfl⟩ := (coordinatePairWords e n r).surjective b
  exact congrArg (fun M => M u v) h

theorem physicalPairMatrix_mul (e : Fin d ≃ C) (n r : ℕ)
    (T S : Register (Fin (n+r) → C) →L[ℂ] Register (Fin (n+r) → C)) :
    physicalPairMatrix e n r (T*S) = physicalPairMatrix e n r T * physicalPairMatrix e n r S := by
  ext a b
  simp only [physicalPairMatrix, ContinuousLinearMap.mul_apply, Matrix.mul_apply]
  rw [register_operator_expansion]
  exact ((coordinatePairWords e n r).sum_comp (fun w =>
    T (lp.single 2 w 1) (coordinatePairWords e n r a) *
      S (lp.single 2 (coordinatePairWords e n r b) 1) w)).symm

theorem physicalPairMatrix_smul (e : Fin d ≃ C) (n r : ℕ) (c : ℂ)
    (T : Register (Fin (n+r) → C) →L[ℂ] Register (Fin (n+r) → C)) :
    physicalPairMatrix e n r (c • T) = c • physicalPairMatrix e n r T := rfl

theorem physicalPairMatrix_frame (e : Fin d ≃ C) (n r : ℕ)
    (T : TensorSpace (n+r) d →L[ℂ] TensorSpace (n+r) d) :
    physicalPairMatrix e n r
      (operatorConjugation (tensorFrame (coordinateFrame e).orthonormal (n+r)).toContinuousLinearMap T) =
      pairOperatorMatrix (n:=n) (r:=r) T := by
  ext a b
  rw [physicalPairMatrix, coordinate_operator_coefficient]
  simp only [coordinatePairWords, coordinateWords, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply, pairOperatorMatrix]

theorem tensorFrame_projector_conjugation
    (u : OrthonormalBasis (Fin d) ℂ (Register C)) (L : ℕ) :
    operatorConjugation (tensorFrame u.orthonormal L).toContinuousLinearMap (projector L d) =
      physicalProjector L := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := tensorFrame_surjective (L:=L) u x
  change tensorFrame u.orthonormal L (projector L d
    ((tensorFrame u.orthonormal L).toContinuousLinearMap.adjoint (tensorFrame u.orthonormal L y))) = _
  rw [isometry_adjoint_apply_self, tensorFrame_physicalProjector]

theorem physicalPairMatrix_projector (e : Fin d ≃ C) (n r : ℕ) :
    physicalPairMatrix e n r (physicalProjector (n+r)) = splitSymmetricProjector n r d := by
  rw [← tensorFrame_projector_conjugation (coordinateFrame e),
    physicalPairMatrix_frame, pairOperatorMatrix_projector]

theorem column_operator_coefficient {L d : ℕ}
    (X : Matrix (Occupation L d) (Occupation L d) ℂ) (a b : Word L d) :
    ofMatrix (@column L d) X (lp.single 2 b 1) a =
      (columnMatrix L d * X * (columnMatrix L d).conjTranspose) a b := by
  simp only [ofMatrix_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.inner_single_right, RCLike.inner_apply, starRingEnd_apply, one_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, columnMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem physicalEmbedding_conjugation_matrix {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A))) (L : ℕ)
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
theorem physicalPairMatrix_slotInsertion {s : ℕ} (e : Fin (s+1) ≃ A×A) (n r : ℕ)
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
theorem sectorChannel_physical_sandwich {s : ℕ} (e : Fin (s+1) ≃ A×A) (n r : ℕ)
    (X : Matrix (Occupation n (s+1)) (Occupation n (s+1)) ℂ) :
    conjugationLinearMap (physicalEmbedding (coordinateFrame e) (n+r)).toContinuousLinearMap
      ((sectorChannel n r s).toLinearMap (registerLiftCLM X)) =
    ((((n+s).choose s : ℝ) / ((n+r+s).choose s : ℝ) : ℝ) : ℂ) •
      conjugationLinearMap (physicalProjector (C:=A×A) (n+r))
        (registerLiftCLM (slotInsertion n r (matrixOf (registerBasis _)
          (operatorConjugation (groupedEmbedding (coordinateFrame e) n).toContinuousLinearMap
            (registerLiftCLM X).1)))) := by
  rw [sectorChannel_apply]
  apply Subtype.ext
  change operatorConjugation (physicalEmbedding (coordinateFrame e) (n+r)).toContinuousLinearMap
      (registerLiftCLM ((wernerChannel n r s).toFun X)).1 = _
  rw [physicalEmbedding_conjugation_matrix]
  have hp : (physicalProjector (C:=A×A) (n+r)).adjoint = physicalProjector (n+r) :=
    (isStarProjection_starProjection (U:=physicalSymmetric (C:=A×A) (n+r))).isSelfAdjoint.adjoint_eq
  have hc (T : Register (Fin (n+r) → A×A) →L[ℂ] Register (Fin (n+r) → A×A)) :
      operatorConjugation (physicalProjector (C:=A×A) (n+r)) T =
        physicalProjector (n+r) * T * physicalProjector (n+r) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [operatorConjugation_apply, hp, ContinuousLinearMap.mul_apply]
  change _ = ((((n+s).choose s : ℝ) / ((n+r+s).choose s : ℝ) : ℝ) : ℂ) •
    operatorConjugation (physicalProjector (C:=A×A) (n+r)) _
  rw [hc]
  apply physicalPairMatrix_injective e n r
  rw [physicalPairMatrix_frame, pairOperatorMatrix_ofMatrix,
    physicalPairMatrix_smul, physicalPairMatrix_mul, physicalPairMatrix_mul,
    physicalPairMatrix_projector, physicalPairMatrix_slotInsertion]
  simpa only [Complex.coe_smul] using wernerChannel_physical_sandwich n r s X

end Cloning.PCTGlobal
