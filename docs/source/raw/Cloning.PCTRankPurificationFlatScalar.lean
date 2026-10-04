import Cloning.PCTRankPurificationMoment

/-! Scalar tensor inputs for the actual square Haar purification channel. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Cloning.PCTRankPurification
open Cloning.PCTPurificationChannel Cloning.MatrixFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem tensorPower_smul_complex (n : ℕ) (c : ℂ) (X : Matrix A B ℂ) :
    tensorPower n (c • X)=c^n • tensorPower n X := by
  ext a b
  simp [tensorPower,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

variable [Nonempty A]
theorem rectangularHaarMoment_one (n : ℕ) :
    rectangularHaarMoment n (1 : Matrix A A ℂ)=haarMoment (A:=A) n := by
  simp only [rectangularHaarMoment,Matrix.mul_one,haarMoment,integralMoment]
  rfl

theorem haarPurificationChannel_scalar_one (n : ℕ) (c : ℂ) :
    (haarPurificationChannel (A:=A) n).toFun (c • (1 : Matrix (Fin n → A) (Fin n → A) ℂ))=
      c • rectangularHaarMoment n (1 : Matrix A A ℂ) := by
  rw [(haarPurificationChannel (A:=A) n).map_smul,haarPurificationChannel_apply,
    purificationMap,Matrix.one_kronecker_one,Matrix.mul_one,sqrt_mul_self (haarMoment_posSemidef n),
    rectangularHaarMoment_one]

theorem haarPurificationChannel_scalar_tensor (n : ℕ) (c : ℂ) :
    (haarPurificationChannel (A:=A) n).toFun (tensorPower n (c • (1 : Matrix A A ℂ)))=
      c^n • rectangularHaarMoment n (1 : Matrix A A ℂ) := by
  rw [tensorPower_smul_complex,tensorPower_one,haarPurificationChannel_scalar_one]

end Cloning.PCTRankPurification
