import Cloning.PCTRankOnePureInput
import Cloning.TensorRankOneGibbs
import Cloning.TensorCloningGlobalCovariance
import Cloning.PhysicalFlatPinchingOrbit

/-! Literal pure Werner covariance and first-column pure-state transport. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical
namespace Cloning.TensorLie
open Cloning.PCT Cloning.PCTRankAdapted Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass Cloning.PCTPurificationChannel Cloning.PCTRankOne
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

@[simp] theorem tensorMap_eq_tensorOperator (n d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    tensorMap n U=tensorOperator n U := by
  ext x w
  simp only [tensorMap_apply,tensorOperator_apply,mul_comm]

/-- Covariance follows from the proved rectangular compression identity and
the literal inverse unitary, including arbitrary selected input slots. -/
theorem pureWernerOutput_unitary {d s L : ℕ} (hcard : Fintype.card (Fin d)=s+1)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (ψ : Register (Fin d)) (hψ : ‖ψ‖=1) (S : Finset (Fin L)) :
    pureWernerOutput hcard (matrixRegister U ψ) ((matrixRegister_norm U hU ψ).trans hψ) S=
      conjugationLinearMap (tensorOperator L U) (pureWernerOutput hcard ψ hψ S) := by
  have hUU : U*Uᴴ=1 := mul_eq_one_comm.mp hU
  have hUs : Uᴴᴴ*Uᴴ=1 := by simpa only [Matrix.conjTranspose_conjTranspose] using hUU
  have hvec : matrixRegister Uᴴ (matrixRegister U ψ)=ψ := by
    change ((matrixRegister Uᴴ).comp (matrixRegister U)) ψ=ψ
    rw [← matrixRegister_mul,hU,matrixRegister_one]
    rfl
  have h := pureWernerOutput_compression hcard hcard Uᴴ hUs (matrixRegister U ψ)
    ((matrixRegister_norm U hU ψ).trans hψ) S
  have hs : supportFactor S.card L s s=1 := div_self (wernerScale_pos S.card L s).ne'
  apply Subtype.ext
  have he := congrArg Subtype.val h
  change operatorConjugation (tensorMap L Uᴴ).adjoint
      (pureWernerOperator s (matrixRegister Uᴴ (matrixRegister U ψ)) S)=
    (supportFactor S.card L s s:ℂ) • pureWernerOperator s (matrixRegister U ψ) S at he
  rw [hvec,tensorMap_adjoint,Matrix.conjTranspose_conjTranspose,tensorMap_eq_tensorOperator,
    hs,Complex.ofReal_one,one_smul] at he
  exact he.symm

/-- Every pure vector is the actual first column of a unitary. -/
theorem exists_unitary_first_column (k : ℕ) (ψ : Register (Fin (1+k))) (hψ : ‖ψ‖=1) :
    ∃ U : unitary (Matrix (Fin (1+k)) (Fin (1+k)) ℂ),
      matrixRegister (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ)
        (registerBasis (Fin (1+k)) 0)=ψ := by
  obtain ⟨U,hU⟩ := Cloning.PhysicalFlatGrassmann.exists_unitary_isometry 1 k
    (pureColumn ψ) (pureColumn_isometry ψ hψ)
  refine ⟨U,?_⟩
  ext a
  have he := congrFun (congrFun hU a) 0
  simp only [pureColumn,Matrix.mul_apply,Cloning.PhysicalFlatGrassmann.coordinateInclusion] at he
  simpa only [registerBasis_apply,matrixRegister_single,Fin.castAdd_zero,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using he.symm

theorem matrixTensorPower_pure {d : ℕ} [NeZero d] (n : ℕ) (ψ : Register (Fin d)) :
    matrixTensorPower (Matrix.vecMulVec (fun a=>ψ a) (star (fun a=>ψ a))) n=
      vectorProjector (tensorVector (fun _ : Fin n=>ψ)) := by
  rw [Cloning.PCTPhysicalState.matrixTensorPower_eq_registerLift]
  calc
    _=registerLiftCLM (fun a c=>tensorVector (fun _ : Fin n=>ψ) a*
        star (tensorVector (fun _ : Fin n=>ψ) c)) := by
      congr 1
      ext a c
      simp only [tensorPower,Matrix.vecMulVec_apply,Pi.star_apply,tensorVector_apply,
        star_prod,Finset.prod_mul_distrib]
    _=_ := registerLiftCLM_rankOne _

theorem rankOne_diagonal_eq_basis_projector (k : ℕ) :
    Matrix.diagonal (fun a=>(rankFlatSpectrum 1 k a:ℂ))=
      Matrix.vecMulVec (fun a=>registerBasis (Fin (1+k)) 0 a)
        (star (fun a=>registerBasis (Fin (1+k)) 0 a)) := by
  ext a b
  have ha : a.val<1 ↔ a=0 := by
    constructor
    · intro h; apply Fin.ext; change a.val=0; omega
    · rintro rfl; exact Nat.zero_lt_one
  simp only [Matrix.diagonal_apply,Matrix.vecMulVec_apply,Pi.star_apply,registerBasis_apply,
    lp.single_apply,rankFlatSpectrum,Nat.cast_one,div_one,ha]
  by_cases hab : a=b <;> by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    simp_all [Pi.single_apply]

/-- Literal rotated rank-one tensor inputs are pure product projectors. -/
theorem matrixTensorPower_rankOne_rotated (k n : ℕ)
    (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ) :
    matrixTensorPower (U*Matrix.diagonal (fun a=>(rankFlatSpectrum 1 k a:ℂ))*Uᴴ) n=
      vectorProjector (tensorVector (fun _ : Fin n=>
        matrixRegister U (registerBasis (Fin (1+k)) 0))) := by
  rw [Cloning.PhysicalFlatConverse.matrixTensorPower_conjugate,
    rankOne_diagonal_eq_basis_projector,matrixTensorPower_pure,
    conjugationLinearMap_vectorProjector,← tensorMap_eq_tensorOperator]
  rw [Cloning.PCTRankGlobal.tensorMap_tensorVector]

end Cloning.TensorLie
