import Cloning.PCTRankAdaptedProduct

/-! A one-dimensional purification environment disappears exactly, leaving
the ordinary finite pure-state Werner cloner on the physical system. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix ComplexOrder
namespace Cloning.PCTRankOne
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.PCTRankAdapted
open Cloning.FiniteKrausLift Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [DecidableEq A]

def singletonInsertion : Matrix (A×Fin 1) A ℂ := fun ab a => if ab.1=a then 1 else 0

theorem singletonInsertion_isometry :
    (singletonInsertion (A:=A))ᴴ*singletonInsertion (A:=A)=(1 : Matrix A A ℂ) := by
  ext a c
  by_cases h : a=c
  · subst c
    simp [singletonInsertion,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply]
  · simp [singletonInsertion,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,h,Ne.symm h]

theorem singletonSlice_regroup (L : ℕ) :
    (environmentSlice (fun _ : Fin L => (0 : Fin 1))).comp
      (regroup (A:=A) (B:=Fin 1) L).toContinuousLinearMap=
      (tensorMap L (singletonInsertion (A:=A))).adjoint := by
  apply register_rect_ext
  intro w a
  rw [ContinuousLinearMap.comp_apply,environmentSlice_apply]
  change regroup L (lp.single 2 w 1) (a,fun _ => (0 : Fin 1))=_
  rw [regroup_apply,tensorMap_adjoint]
  have he : (fun i => (a i,(0 : Fin 1)))=w ↔ ∀i,(w i).1=a i := by
    constructor
    · intro h i
      exact (congrArg Prod.fst (congrFun h i)).symm
    · intro h
      funext i
      exact Prod.ext (h i).symm (Subsingleton.elim _ _)
  simp [tensorMap,matrixRegister_single,tensorPower,Matrix.conjTranspose_apply,
    singletonInsertion,apply_ite,Fintype.prod_ite_zero,lp.single_apply,Pi.single_apply,he]

theorem reduceOutput_singleton (L : ℕ) (X : TraceClass (Register (Fin L → A×Fin 1))) :
    reduceOutput L X=conjugationLinearMap (tensorMap L (singletonInsertion (A:=A))).adjoint X := by
  unfold reduceOutput partialTraceLinear
  simp only [LinearMap.sum_apply,Fintype.sum_unique]
  rw [show (default : Fin L → Fin 1)=(fun _ => (0 : Fin 1)) from Subsingleton.elim _ _,
    Cloning.PCTGlobal.conjugation_comp,singletonSlice_regroup]

/-- Finite equality of the actual reduced Werner output and the system-only
Werner output when the purification environment has dimension one. -/
theorem reducedWernerOutput_singleton {L s : ℕ} (hA : Fintype.card A=s+1)
    (ψ : Register A) (hψ : ‖ψ‖=1) (S : Finset (Fin L)) :
    reducedWernerOutput (by simpa using hA : Fintype.card (A×Fin 1)=s+1)
      (matrixRegister (singletonInsertion (A:=A)) ψ)
      ((matrixRegister_norm _ singletonInsertion_isometry ψ).trans hψ) S=
      pureWernerOutput hA ψ hψ S := by
  change reduceOutput L (pureWernerOutput _ _ _ S)=_
  rw [reduceOutput_singleton,pureWernerOutput_compression hA
    (by simpa using hA : Fintype.card (A×Fin 1)=s+1)
    (singletonInsertion (A:=A)) singletonInsertion_isometry ψ hψ S]
  have hscale : supportFactor S.card L s s=1 :=
    div_self (wernerScale_pos S.card L s).ne'
  rw [hscale,Complex.ofReal_one,one_smul]

end Cloning.PCTRankOne
