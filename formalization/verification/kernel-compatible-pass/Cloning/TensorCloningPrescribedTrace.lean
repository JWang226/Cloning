import Cloning.PCTCountMeasurementChannel
import Cloning.PCTRankAdaptedPartialTrace
import Cloning.MatrixPartialTraceCovariance

/-! Literal finite-register partial trace after a computational relabeling. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix Kronecker Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
open Cloning.PCTPurificationChannel Cloning.FiniteKrausLift Cloning.Compression
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]

def relabelIsometry (e : I ≃ J) : Register I →ₗᵢ[ℂ] Register J :=
  ((registerBasis J).orthonormal.comp e e.injective).orthogonalFamily.linearIsometry

@[simp] theorem relabelIsometry_single (e : I ≃ J) (i : I) :
    relabelIsometry e (lp.single 2 i 1)=lp.single 2 (e i) 1 := by
  rw [relabelIsometry, OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply,one_smul,Function.comp_apply,registerBasis_apply]

@[simp] theorem relabelIsometry_apply (e : I ≃ J) (x : Register I) (j : J) :
    relabelIsometry e x j=x (e.symm j) := by
  rw [relabelIsometry, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp only [Function.comp_apply, LinearIsometry.toSpanSingleton_apply, registerBasis_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply, Pi.single_apply]
  have he i : j=e i ↔ i=e.symm j := by rw [eq_comm, e.apply_eq_iff_eq_symm_apply]
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem relabelIsometry_adjoint_single (e : I ≃ J) (j : J) :
    (relabelIsometry e).toContinuousLinearMap.adjoint (lp.single 2 j 1)=lp.single 2 (e.symm j) 1 := by
  have he : lp.single 2 j 1=relabelIsometry e (lp.single 2 (e.symm j) 1) := by simp
  rw [he, isometry_adjoint_apply_self]

theorem relabel_registerLift (e : I ≃ J) (X : Matrix I I ℂ) :
    conjugationLinearMap (relabelIsometry e).toContinuousLinearMap (registerLiftCLM X)=
      registerLiftCLM (fun a b => X (e.symm a) (e.symm b)) := by
  apply Subtype.ext
  apply register_operator_ext
  intro a b
  change relabelIsometry e ((registerLiftCLM X).1
    ((relabelIsometry e).toContinuousLinearMap.adjoint (lp.single 2 b 1))) a = _
  rw [relabelIsometry_adjoint_single, relabelIsometry_apply, registerLiftCLM_coefficient,
    registerLiftCLM_coefficient]

def discardChannel (e : I ≃ A × B) : QuantumChannel (Register I) (Register A) :=
  partialTraceChannel.comp (QuantumChannel.ofIsometry (relabelIsometry e))

theorem discardChannel_registerLift (e : I ≃ A × B) (X : Matrix I I ℂ) :
    (discardChannel e).toLinearMap (registerLiftCLM X)=
      registerLiftCLM (partialTrace (fun a b => X (e.symm a) (e.symm b))) := by
  change partialTraceLinear (conjugationLinearMap (relabelIsometry e).toContinuousLinearMap
    (registerLiftCLM X))=_
  rw [relabel_registerLift, Cloning.PCTRankAdapted.partialTraceLinear_registerLift]

theorem discardChannel_coefficient (e : I ≃ A × B) (X : TraceClass (Register I)) (a c : A) :
    ((discardChannel e).toLinearMap X).1 (lp.single 2 c 1) a=
      ∑ b, X.1 (lp.single 2 (e.symm (c,b)) 1) (e.symm (a,b)) := by
  change (partialTraceLinear (conjugationLinearMap (relabelIsometry e).toContinuousLinearMap X)).1
    (lp.single 2 c 1) a=_
  rw [partialTraceLinear_coefficient]
  apply Finset.sum_congr rfl
  intro b _
  change relabelIsometry e (X.1 ((relabelIsometry e).toContinuousLinearMap.adjoint
    (lp.single 2 (c,b) 1))) (a,b)=_
  rw [relabelIsometry_adjoint_single,relabelIsometry_apply]

theorem discardChannel_covariant (e : I ≃ A × B) (U : Matrix I I ℂ)
    (S : Matrix A A ℂ) (T : Matrix B B ℂ) (hT : Tᴴ*T=1)
    (hU : U.submatrix e.symm e.symm = S ⊗ₖ T) (X : TraceClass (Register I)) :
    (discardChannel e).toLinearMap (conjugationLinearMap (matrixRegister U) X)=
      conjugationLinearMap (matrixRegister S) ((discardChannel e).toLinearMap X) := by
  have hX := Cloning.PCTCountMeasurement.registerLift_matrixOf X
  rw [← hX,conjugation_matrixRegister,discardChannel_registerLift,
    discardChannel_registerLift,conjugation_matrixRegister]
  congr 1
  have hm (M N : Matrix I I ℂ) : (M*N).submatrix e.symm e.symm=
      M.submatrix e.symm e.symm * N.submatrix e.symm e.symm :=
    (Matrix.submatrix_mul_equiv M N e.symm e.symm e.symm).symm
  have hs : Uᴴ.submatrix e.symm e.symm=(U.submatrix e.symm e.symm)ᴴ := rfl
  change partialTrace ((U * matrixOf (registerBasis I) X.1 * Uᴴ).submatrix e.symm e.symm)=_
  rw [hm,hm,hs,hU,partialTrace_tensor_conjugation S T _ hT]
  rfl

end Cloning.TensorCloning
