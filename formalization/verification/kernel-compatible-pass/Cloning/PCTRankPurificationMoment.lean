import Cloning.PCTRankPurificationCompletion
import Cloning.PCTPurificationChannelHaar

/-! Rectangular Haar tensor moments for a genuinely smaller purification environment. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace Cloning.PCTRankPurification
open Cloning.PCTPurificationChannel Cloning.Compression
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance matrixCStar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def rectangularTensor (n : ℕ) (T : Matrix A B ℂ) : (Fin n → A)×(Fin n → B) → ℂ :=
  fun ab => tensorPower n T ab.1 ab.2

def rectangularMoment (n : ℕ) (T : Matrix A B ℂ) :=
  Matrix.vecMulVec (rectangularTensor n T) (star (rectangularTensor n T))

theorem rectangularMoment_posSemidef (n : ℕ) (T : Matrix A B ℂ) :
    (rectangularMoment n T).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

theorem partialTrace_rectangularMoment (n : ℕ) (T : Matrix A B ℂ) :
    partialTrace (rectangularMoment n T) = tensorPower n (T*Tᴴ) := by
  rw [tensorPower_mul,tensorPower_star]
  ext a c
  rfl

def rectangularLeftTensor (n : ℕ) (V : Matrix A A ℂ) :
    Matrix ((Fin n → A)×(Fin n → B)) ((Fin n → A)×(Fin n → B)) ℂ :=
  tensorPower n V ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ)

theorem rectangularTensor_mul (n : ℕ) (V : Matrix A A ℂ) (T : Matrix A B ℂ) :
    rectangularTensor n (V*T)=rectangularLeftTensor (B := B) n V *ᵥ rectangularTensor n T := by
  funext ⟨a,b⟩
  rw [rectangularTensor,tensorPower_mul]
  simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct,rectangularLeftTensor,
    Matrix.kronecker_apply,Matrix.one_apply,rectangularTensor,Fintype.sum_prod_type,
    mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]

theorem rectangularMoment_mul (n : ℕ) (V : Matrix A A ℂ) (T : Matrix A B ℂ) :
    rectangularMoment n (V*T)=rectangularLeftTensor (B := B) n V * rectangularMoment n T *
      (rectangularLeftTensor (B := B) n V)ᴴ := by
  unfold rectangularMoment
  rw [rectangularTensor_mul,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,
    Matrix.vecMul_conjTranspose,star_star]

variable [Nonempty A]

def rectangularHaarMoment (n : ℕ) (J : Matrix A B ℂ) :=
  ∫ U : unitary (Matrix A A ℂ), rectangularMoment n ((U : Matrix A A ℂ)*J) ∂unitaryHaar

theorem continuous_rectangularMoment (n : ℕ) (J : Matrix A B ℂ) :
    Continuous (fun U : unitary (Matrix A A ℂ) => rectangularMoment n ((U : Matrix A A ℂ)*J)) := by
  unfold rectangularMoment rectangularTensor tensorPower
  fun_prop

theorem integrable_rectangularMoment (n : ℕ) (J : Matrix A B ℂ) :
    Integrable (fun U : unitary (Matrix A A ℂ) => rectangularMoment n ((U : Matrix A A ℂ)*J))
      unitaryHaar :=
  (continuous_rectangularMoment n J).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem rectangularHaarMoment_posSemidef (n : ℕ) (J : Matrix A B ℂ) :
    (rectangularHaarMoment n J).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact integral_nonneg (fun U => (rectangularMoment_posSemidef n _).nonneg)

theorem partialTrace_rectangularHaarMoment (n : ℕ) (J : Matrix A B ℂ) :
    partialTrace (rectangularHaarMoment n J) =
      ∫ U : unitary (Matrix A A ℂ), tensorPower n ((U : Matrix A A ℂ)*(J*Jᴴ)*U.valᴴ) ∂unitaryHaar := by
  have hh := (partialTraceCLM (A := Fin n → A) (B := Fin n → B)).integral_comp_comm
    (integrable_rectangularMoment n J)
  change (∫ U : unitary (Matrix A A ℂ), partialTrace (rectangularMoment n (U.val*J)) ∂unitaryHaar) =
    partialTrace (rectangularHaarMoment n J) at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [partialTrace_rectangularMoment]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem rectangularHaarMoment_unitary_invariant (n : ℕ) (J : Matrix A B ℂ)
    (V : unitary (Matrix A A ℂ)) :
    rectangularLeftTensor (B := B) n V * rectangularHaarMoment n J *
      (rectangularLeftTensor (B := B) n V)ᴴ = rectangularHaarMoment n J := by
  have hh := (matrixSandwichCLM (rectangularLeftTensor (B := B) n V)).integral_comp_comm
    (integrable_rectangularMoment n J)
  change (∫ U : unitary (Matrix A A ℂ), rectangularLeftTensor (B := B) n V *
    rectangularMoment n (U.val*J)*(rectangularLeftTensor (B := B) n V)ᴴ ∂unitaryHaar)=
    rectangularLeftTensor (B := B) n V*rectangularHaarMoment n J*
      (rectangularLeftTensor (B := B) n V)ᴴ at hh
  rw [← hh]
  simp_rw [← rectangularMoment_mul,← Matrix.mul_assoc]
  exact integral_mul_left_eq_self (μ := unitaryHaar)
    (fun U : unitary (Matrix A A ℂ) => rectangularMoment n (U.val*J)) V

end Cloning.PCTRankPurification
