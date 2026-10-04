import Cloning.PCTRankAdaptedWerner

/-! Rectangular system compression commutes exactly with the physical
partial trace, including the actual regrouping of all tensor slots. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass Cloning.Compression
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem partialTrace_rectangular (J : Matrix B A ℂ)
    (X : Matrix (A × E) (A × E) ℂ) :
    partialTrace ((J ⊗ₖ (1 : Matrix E E ℂ)) * X * (J ⊗ₖ (1 : Matrix E E ℂ))ᴴ) =
      J * partialTrace X * Jᴴ := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro T
  calc
    _ = Matrix.trace ((T ⊗ₖ (1 : Matrix E E ℂ)) *
        ((J ⊗ₖ (1 : Matrix E E ℂ)) * X * (J ⊗ₖ (1 : Matrix E E ℂ))ᴴ)) := (trace_tensor_pairing T _).symm
    _ = Matrix.trace (((J ⊗ₖ (1 : Matrix E E ℂ))ᴴ *
        (T ⊗ₖ (1 : Matrix E E ℂ)) * (J ⊗ₖ (1 : Matrix E E ℂ))) * X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((Jᴴ * T * J) ⊗ₖ (1 : Matrix E E ℂ)) * X) := by
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [Matrix.one_mul, Matrix.mul_one]
    _ = Matrix.trace ((Jᴴ * T * J) * partialTrace X) := trace_tensor_pairing _ X
    _ = Matrix.trace (T * (J * partialTrace X * Jᴴ)) := by
      calc
        _ = Matrix.trace (Jᴴ * (T * (J * partialTrace X))) := by simp only [Matrix.mul_assoc]
        _ = Matrix.trace ((T * (J * partialTrace X)) * Jᴴ) := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]

theorem partialTraceLinear_registerLift (X : Matrix (A × E) (A × E) ℂ) :
    partialTraceLinear (registerLiftCLM X) = registerLiftCLM (partialTrace X) := by
  apply Subtype.ext
  apply register_operator_ext
  intro a c
  simp only [partialTraceLinear_coefficient, registerLiftCLM_coefficient, partialTrace]

theorem partialTraceLinear_conjugation (J : Matrix B A ℂ)
    (X : TraceClass (Register (A × E))) :
    partialTraceLinear (conjugationLinearMap (matrixRegister (J ⊗ₖ (1 : Matrix E E ℂ))) X) =
      conjugationLinearMap (matrixRegister J) (partialTraceLinear X) := by
  obtain ⟨M,rfl⟩ : ∃ M : Matrix (A × E) (A × E) ℂ, registerLiftCLM M = X :=
    ⟨Cloning.InfiniteFiniteCorner.matrixOf (registerBasis _) X.1,
      Cloning.PCTGlobal.registerLiftCLM_matrixOf X⟩
  rw [conjugation_matrixRegister, partialTraceLinear_registerLift,
    partialTraceLinear_registerLift, conjugation_matrixRegister, partialTrace_rectangular]

theorem register_rect_ext {X Y : Register A →L[ℂ] Register B}
    (h : ∀ a b, X (lp.single 2 a 1) b = Y (lp.single 2 a 1) b) : X = Y := by
  ext x b
  have hx : x = ∑ a, x a • (lp.single 2 a 1 : Register A) := by
    ext a
    simp [lp.single_apply, Pi.single_apply]
  rw [hx]
  simp only [map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, h]

theorem regroup_single_rect (L : ℕ) (w : Fin L → A × E) :
    regroup L (lp.single 2 w 1) = lp.single 2 (pairWordsEquiv L w) 1 := by
  rw [regroup, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

theorem regroup_tensorMap (L : ℕ) (J : Matrix B A ℂ) :
    (regroup (A:=B) (B:=E) L).toContinuousLinearMap.comp
      (tensorMap L (J ⊗ₖ (1 : Matrix E E ℂ))) =
      (matrixRegister (tensorPower L J ⊗ₖ (1 : Matrix (Fin L → E) (Fin L → E) ℂ))).comp
        (regroup (A:=A) (B:=E) L).toContinuousLinearMap := by
  apply register_rect_ext
  intro w v
  rcases v with ⟨a,b⟩
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    regroup_apply, tensorMap, matrixRegister_single, regroup_single_rect,
    Matrix.kroneckerMap_apply, tensorPower, Finset.prod_mul_distrib]
  congr 1
  change tensorPower L (1 : Matrix E E ℂ) b (fun i => (w i).2) = _
  rw [tensorPower_one]
  rfl

/-- Physical reduction, with the system and environment grouped only inside
the channel. -/
def reduceOutput (L : ℕ) (X : TraceClass (Register (Fin L → A × E))) :
    TraceClass (Register (Fin L → A)) :=
  partialTraceLinear (conjugationLinearMap (regroup L).toContinuousLinearMap X)

theorem reduceOutput_conjugation (L : ℕ) (J : Matrix B A ℂ)
    (X : TraceClass (Register (Fin L → A × E))) :
    reduceOutput L (conjugationLinearMap (tensorMap L (J ⊗ₖ (1 : Matrix E E ℂ))) X) =
      conjugationLinearMap (tensorMap L J) (reduceOutput L X) := by
  unfold reduceOutput
  rw [Cloning.PCTGlobal.conjugation_comp, regroup_tensorMap,
    ← Cloning.PCTGlobal.conjugation_comp, partialTraceLinear_conjugation]
  rfl

end Cloning.PCTRankAdapted
