import Cloning.FiniteKrausLift
import Cloning.PurificationSupport

/-! A fixed computational one-particle frame and its literal tensor relabeling. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
open Cloning.InfiniteTraceClass Cloning.PCT Cloning.InfiniteFiniteCorner
open Cloning.GeneralSymmetricOccupation Cloning.PCTPurificationChannel
namespace Cloning.PCTGlobal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}

def coordinateFrame (e : Fin d ≃ C) : OrthonormalBasis (Fin d) ℂ (Register C) :=
  (registerBasis C).toOrthonormalBasis.reindex e.symm

@[simp] theorem coordinateFrame_apply (e : Fin d ≃ C) (i : Fin d) :
    coordinateFrame e i = registerBasis C (e i) := by
  simp only [coordinateFrame, OrthonormalBasis.reindex_apply, Equiv.symm_symm,
    HilbertBasis.coe_toOrthonormalBasis]

/-- The coordinate frame acts by the actual inverse word relabeling. -/
theorem tensorFrame_coordinate_apply (e : Fin d ≃ C) (L : ℕ)
    (x : TensorSpace L d) (w : Fin L → C) :
    tensorFrame (coordinateFrame e).orthonormal L x w = x (fun i => e.symm (w i)) := by
  rw [tensorFrame_apply]
  have hp (v : Word L d) : (∏ i, coordinateFrame e (v i) (w i)) =
      if v = (fun i => e.symm (w i)) then (1 : ℂ) else 0 := by
    simp only [coordinateFrame_apply, registerBasis_apply, lp.single_apply, Pi.single_apply]
    have he (i : Fin L) : w i = e (v i) ↔ v i = e.symm (w i) := by
      rw [eq_comm, e.apply_eq_iff_eq_symm_apply]
    simp only [he, Fintype.prod_ite_zero, Finset.prod_const_one]
    congr 1
    exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp only [hp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Adjoint tensor relabeling has the forward word coordinates. -/
theorem tensorFrame_coordinate_adjoint_apply (e : Fin d ≃ C) (L : ℕ)
    (x : Register (Fin L → C)) (w : Word L d) :
    (tensorFrame (coordinateFrame e).orthonormal L).toContinuousLinearMap.adjoint x w =
      x (fun i => e (w i)) := by
  obtain ⟨y, rfl⟩ := tensorFrame_surjective (L := L) (coordinateFrame e) x
  rw [isometry_adjoint_apply_self, tensorFrame_coordinate_apply]
  simp only [Equiv.symm_apply_apply]

/-- Computational entries of arbitrary framed operators are just relabeled. -/
theorem coordinate_operator_coefficient (e : Fin d ≃ C) (L : ℕ)
    (T : TensorSpace L d →L[ℂ] TensorSpace L d) (a b : Fin L → C) :
    operatorConjugation (tensorFrame (coordinateFrame e).orthonormal L).toContinuousLinearMap T
      (lp.single 2 b 1) a = T (lp.single 2 (fun i => e.symm (b i)) 1)
        (fun i => e.symm (a i)) := by
  have hx : (tensorFrame (coordinateFrame e).orthonormal L).toContinuousLinearMap.adjoint
      (lp.single 2 b 1) = (lp.single 2 (fun i => e.symm (b i)) 1 : TensorSpace L d) := by
    ext w
    rw [tensorFrame_coordinate_adjoint_apply]
    simp only [lp.single_apply, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      exact (e.apply_eq_iff_eq_symm_apply).mp (congrFun h i)
    · intro h
      funext i
      rw [congrFun h i, e.apply_symm_apply]
  change tensorFrame (coordinateFrame e).orthonormal L
    (T ((tensorFrame (coordinateFrame e).orthonormal L).toContinuousLinearMap.adjoint
      (lp.single 2 b 1))) a = _
  rw [tensorFrame_coordinate_apply, hx]

end Cloning.PCTGlobal
