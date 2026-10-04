import Cloning.PCTRankOneAction

/-! Literal pure tensor projectors for the finite rank-one PCT identity. -/
noncomputable section
open scoped BigOperators Classical InnerProductSpace Matrix ComplexOrder
namespace Cloning.PCTRankOne
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.PCTRankAdapted
open Cloning.FiniteKrausLift Cloning.InfiniteTraceClass Cloning.PCTPhysicalState
open Cloning.GeneralSymmetricOccupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def pureColumn (ψ : Register A) : Matrix A (Fin 1) ℂ := fun a _ => ψ a

theorem pureColumn_isometry (ψ : Register A) (hψ : ‖ψ‖=1) :
    (pureColumn ψ)ᴴ*pureColumn ψ=1 := by
  have hi : ⟪ψ,ψ⟫_ℂ=1 := by simp [inner_self_eq_norm_sq_to_K,hψ]
  ext a b
  have hab : a=b := Subsingleton.elim _ _
  subst b
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,pureColumn,
    lp.inner_eq_tsum,tsum_fintype,RCLike.inner_apply,starRingEnd_apply,mul_comm,
    Matrix.one_apply_eq] using hi

@[simp] theorem rankOneVector_pureColumn (ψ : Register A) : rankOneVector (pureColumn ψ)=ψ := by
  ext a
  simp [pureColumn]

theorem embeddedRankOne_matrix (J : Matrix A (Fin 1) ℂ) (hJ : Jᴴ*J=1) :
    (embeddedState J hJ (flatInternalState 0)).matrix=
      Matrix.vecMulVec (fun a => rankOneVector J a) (star (fun a => rankOneVector J a)) := by
  change J*(flatInternalState 0).matrix*Jᴴ=_
  rw [PCTRankPurification.flatInternalState_matrix_complex]
  ext a b
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_unique,rankOneVector_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,Complex.star_def]

theorem tensorState_rankOne_eq_projector (J : Matrix A (Fin 1) ℂ) (hJ : Jᴴ*J=1) (n : ℕ) :
    (tensorState (embeddedState J hJ (flatInternalState 0)) n).1=
      vectorProjector (tensorVector (fun _ : Fin n => rankOneVector J)) := by
  change registerLiftCLM (tensorPower n (embeddedState J hJ (flatInternalState 0)).matrix)=_
  rw [embeddedRankOne_matrix]
  calc
    _=registerLiftCLM (fun a c =>
        tensorVector (fun _ : Fin n => rankOneVector J) a*
          star (tensorVector (fun _ : Fin n => rankOneVector J) c)) := by
      congr 1
      ext a c
      simp only [tensorPower,Matrix.vecMulVec_apply,Pi.star_apply,tensorVector_apply,
        star_prod,Finset.prod_mul_distrib]
    _=_ := registerLiftCLM_rankOne _

/-- The prescribed fixed PCT map is exactly the finite Werner pure-state
cloner on every normalized pure product vector, without an action premise. -/
theorem channel_tensorProjector (k n t : ℕ) (ψ : Register (Fin (1+k))) (hψ : ‖ψ‖=1) :
    (Cloning.PhysicalFlatPCT.channel 0 k n t).toLinearMap
      (vectorProjector (tensorVector (fun _ : Fin n => ψ)))=
      pureWernerOutput (by simp [Nat.add_comm] : Fintype.card (Fin (1+k))=k+1) ψ hψ
        (inputSlots n (n+t) (Nat.le_add_right n t)) := by
  have h := channel_pure_product k n t (pureColumn ψ) (pureColumn_isometry ψ hψ)
  rw [tensorState_rankOne_eq_projector] at h
  simpa only [rankOneVector_pureColumn] using h

end Cloning.PCTRankOne
