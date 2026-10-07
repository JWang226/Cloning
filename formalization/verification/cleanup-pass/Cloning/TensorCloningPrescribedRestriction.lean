import Cloning.TensorCloningPrescribedTrace
import Cloning.TensorCloningGlobalCovariance
import Cloning.PCTPhysicalState

/-! Exact tensor-prefix restriction, including all-input covariance and
identity at equal sample size. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix Kronecker Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.TensorLie
open Cloning.PCTPurificationChannel Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.FiniteKrausLift Cloning.Compression
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def prefixWordEquiv (n m d : ℕ) (h : m≤n) :
    (Fin n → Fin d) ≃ (Fin m → Fin d) × (Fin (n-m) → Fin d) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl (Fin d))).trans
    (splitWordsEquiv m (n-m))

theorem tensorPower_prefix (n m d : ℕ) (h : m≤n) (U : Matrix (Fin d) (Fin d) ℂ) :
    (tensorPower n U).submatrix (prefixWordEquiv n m d h).symm (prefixWordEquiv n m d h).symm =
      tensorPower m U ⊗ₖ tensorPower (n-m) U := by
  ext a b
  change (∏ i : Fin n, U
    (Fin.addCases a.1 a.2 ((finCongr (Nat.add_sub_of_le h).symm) i))
    (Fin.addCases b.1 b.2 ((finCongr (Nat.add_sub_of_le h).symm) i))) =
      (∏ i, U (a.1 i) (b.1 i)) * (∏ i, U (a.2 i) (b.2 i))
  rw [(finCongr (Nat.add_sub_of_le h).symm).prod_comp
    (fun i : Fin (m+(n-m)) => U (Fin.addCases a.1 a.2 i) (Fin.addCases b.1 b.2 i))]
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]

def restrictionChannel (n m d : ℕ) (h : m≤n) :
    QuantumChannel (TensorRegister n (Fin d)) (TensorRegister m (Fin d)) :=
  discardChannel (prefixWordEquiv n m d h)

theorem restrictionChannel_coefficient (n m d : ℕ) (h : m≤n)
    (X : TraceClass (TensorRegister n (Fin d))) (a c : Fin m → Fin d) :
    ((restrictionChannel n m d h).toLinearMap X).1 (lp.single 2 c 1) a=
      ∑ b : Fin (n-m) → Fin d,
        X.1 (lp.single 2 ((prefixWordEquiv n m d h).symm (c,b)) 1)
          ((prefixWordEquiv n m d h).symm (a,b)) :=
  discardChannel_coefficient _ X a c

theorem partialTrace_kronecker {A B : Type*} [Fintype A] [Fintype B]
    (M : Matrix A A ℂ) (N : Matrix B B ℂ) : partialTrace (M ⊗ₖ N)=(Matrix.trace N) • M := by
  ext a c
  simp only [partialTrace,Matrix.kronecker_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.trace,Matrix.diag,← Finset.mul_sum]
  ring

theorem restrictionChannel_tensorState {d : ℕ} (n m : ℕ) (h : m≤n)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1))) :
    (restrictionChannel n m (d+1) h).toLinearMap (tensorState ρ n).1=(tensorState ρ m).1 := by
  change (discardChannel _).toLinearMap (registerLiftCLM (tensorPower n ρ.matrix))=
    registerLiftCLM (tensorPower m ρ.matrix)
  rw [discardChannel_registerLift]
  change registerLiftCLM (partialTrace ((tensorPower n ρ.matrix).submatrix
    (prefixWordEquiv n m (d+1) h).symm (prefixWordEquiv n m (d+1) h).symm))=_
  rw [tensorPower_prefix,partialTrace_kronecker,trace_tensorPower,ρ.trace_one,one_pow,one_smul]

theorem matrixRegister_tensorPower (n d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    matrixRegister (tensorPower n U)=tensorOperator n U := by
  ext x w
  simp only [matrixRegister_apply,tensorOperator_apply,tensorPower]

theorem restrictionChannel_covariant (n m d : ℕ) (h : m≤n)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (X : TraceClass (TensorRegister n (Fin d))) :
    (restrictionChannel n m d h).toLinearMap (conjugationLinearMap (tensorOperator n U) X)=
      conjugationLinearMap (tensorOperator m U) ((restrictionChannel n m d h).toLinearMap X) := by
  have hT : (tensorPower (n-m) U)ᴴ*tensorPower (n-m) U=1 := by
    rw [← tensorPower_star,← tensorPower_mul,hU,tensorPower_one]
  simpa only [matrixRegister_tensorPower,restrictionChannel] using
    discardChannel_covariant (prefixWordEquiv n m d h) (tensorPower n U)
      (tensorPower m U) (tensorPower (n-m) U) hT (tensorPower_prefix n m d h U) X

theorem restrictionChannel_self (n d : ℕ) (h : n≤n) (X : TraceClass (TensorRegister n (Fin d))) :
    (restrictionChannel n n d h).toLinearMap X=X := by
  apply Subtype.ext
  apply register_operator_ext
  intro a c
  rw [restrictionChannel_coefficient]
  have he (w : Fin n → Fin d) (z : Fin (n-n) → Fin d) :
      (prefixWordEquiv n n d h).symm (w,z)=w := by
    funext i
    change Fin.addCases w z (Fin.cast (Nat.add_sub_of_le h).symm i)=w i
    have hi : Fin.cast (Nat.add_sub_of_le h).symm i=Fin.castAdd (n-n) i := Fin.ext rfl
    rw [hi,Fin.addCases_left]
  simp only [he,Finset.sum_const,Fintype.card_fun,Fintype.card_fin,Nat.sub_self,pow_zero,
    Finset.card_univ,one_nsmul]

end Cloning.TensorCloning
