import Cloning.PCTPurificationChannel

/-! A square-root moment normalized on a physical support projection extends
canonically to an all-input channel by preparing a fixed state on its complement. -/
noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder
namespace Cloning.PCTRankPurification
open Cloning.Channels Cloning.Compression Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Rank-one output preparation after measuring a row of the rejected support. -/
def complementKraus (P : Matrix A A ℂ) (b0 : B) (a : A) : Matrix B A ℂ :=
  fun b c => if b=b0 then (1-P) a c else 0

theorem complementKraus_normalization (P : Matrix A A ℂ) (hP : Pᴴ=P)
    (hPP : P*P=P) (b0 : B) :
    ∑ a, (complementKraus P b0 a)ᴴ*complementKraus P b0 a = 1-P := by
  have he : (1-P)ᴴ*(1-P)=1-P := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP]
    noncomm_ring [hPP]
  calc
    _ = (1-P)ᴴ*(1-P) := by
      ext a c
      simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,complementKraus]
      simp
    _ = _ := he

def supportedPurificationKraus (R : Matrix (A×B) (A×B) ℂ)
    (P : Matrix A A ℂ) (b0 : A×B) : Sum B A → Matrix (A×B) A ℂ :=
  Sum.elim (purificationKraus R) (complementKraus P b0)

theorem supportedPurificationKraus_normalization
    (R : Matrix (A×B) (A×B) ℂ) (hR : R.PosSemidef)
    (P : Matrix A A ℂ) (hP : Pᴴ=P) (hPP : P*P=P)
    (htrace : partialTrace R=P) (b0 : A×B) :
    ∑ i, (supportedPurificationKraus R P b0 i)ᴴ*supportedPurificationKraus R P b0 i = 1 := by
  rw [Fintype.sum_sum_type]
  change (∑ b,(purificationKraus R b)ᴴ*purificationKraus R b)+
    (∑ a,(complementKraus P b0 a)ᴴ*complementKraus P b0 a)=1
  rw [purificationKraus_normalization hR,htrace,complementKraus_normalization P hP hPP]
  abel

/-- A genuine CPTP map on all input matrices, including the rejected sectors. -/
def supportedPurificationChannel
    (R : Matrix (A×B) (A×B) ℂ) (hR : R.PosSemidef)
    (P : Matrix A A ℂ) (hP : Pᴴ=P) (hPP : P*P=P)
    (htrace : partialTrace R=P) (b0 : A×B) : MatrixChannel A (A×B) :=
  ofKraus (supportedPurificationKraus R P b0)
    (supportedPurificationKraus_normalization R hR P hP hPP htrace b0)

theorem complementKraus_mul_eq_zero (P X : Matrix A A ℂ) (hX : (1-P)*X=0)
    (b0 : B) (a : A) : complementKraus P b0 a*X=0 := by
  ext b c
  by_cases hb : b=b0
  · subst b
    simpa [complementKraus,Matrix.mul_apply] using congrArg (fun M => M a c) hX
  · simp [complementKraus,Matrix.mul_apply,hb]

/-- On supported inputs the completion has exactly the intended square-root action. -/
theorem supportedPurificationChannel_apply_supported
    (R : Matrix (A×B) (A×B) ℂ) (hR : R.PosSemidef)
    (P : Matrix A A ℂ) (hP : Pᴴ=P) (hPP : P*P=P)
    (htrace : partialTrace R=P) (b0 : A×B)
    (X : Matrix A A ℂ) (hX : P*X=X) :
    (supportedPurificationChannel R hR P hP hPP htrace b0).toFun X = purificationMap R X := by
  change krausMap (supportedPurificationKraus R P b0) X = _
  unfold krausMap
  rw [Fintype.sum_sum_type]
  change (∑ b,purificationKraus R b*X*(purificationKraus R b)ᴴ)+
    (∑ a,complementKraus P b0 a*X*(complementKraus P b0 a)ᴴ)=_
  have hx : (1-P)*X=0 := by rw [Matrix.sub_mul,Matrix.one_mul,hX,sub_self]
  simp only [complementKraus_mul_eq_zero P X hx,Matrix.zero_mul,Finset.sum_const_zero,add_zero]
  exact (purificationMap_eq_kraus R X).symm

end Cloning.PCTRankPurification
