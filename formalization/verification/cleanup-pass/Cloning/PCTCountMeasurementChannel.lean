import Cloning.PCTCountMeasurementWeights
import Cloning.FiniteKrausLift
import Cloning.InfiniteChannelFidelity

/-! The finite computational measurement followed by a deterministic label is
an explicit all-input CPTP map, with literal rectangular Kraus matrices. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical ComplexOrder
namespace Cloning.PCTCountMeasurement
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def measurementKraus (label : I → J) (i : I) : Matrix J I ℂ :=
  fun a b => if a=label i then (if b=i then 1 else 0) else 0

theorem measurementKraus_gram (label : I → J) (i a b : I) :
    ((measurementKraus label i)ᴴ * measurementKraus label i) a b =
      if a=i ∧ b=i then 1 else 0 := by
  by_cases ha : a=i <;> by_cases hb : b=i <;>
    simp [measurementKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, ha, hb]

theorem measurementKraus_normalization (label : I → J) :
    ∑ i, (measurementKraus label i)ᴴ * measurementKraus label i = 1 := by
  ext a b
  simp only [Matrix.sum_apply, measurementKraus_gram, Matrix.one_apply]
  by_cases hab : a=b
  · subst b; simp
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    have h : ¬(a=i ∧ b=i) := by rintro ⟨rfl,rfl⟩; exact hab rfl
    exact if_neg h

def measuredMatrix (label : I → J) (M : Matrix I I ℂ) : Matrix J J ℂ :=
  Matrix.diagonal (fun j => ∑ i, if label i=j then M i i else 0)

theorem measurementKraus_sandwich (label : I → J) (i : I) (M : Matrix I I ℂ) (a b : J) :
    (measurementKraus label i * M * (measurementKraus label i)ᴴ) a b =
      if a=label i ∧ b=label i then M i i else 0 := by
  have hl (c : I) : (measurementKraus label i * M) a c = if a=label i then M i c else 0 := by
    by_cases ha : a=label i <;> simp [measurementKraus, Matrix.mul_apply, ha]
  simp only [Matrix.mul_apply, hl, Matrix.conjTranspose_apply]
  by_cases ha : a=label i <;> by_cases hb : b=label i <;>
    simp [measurementKraus, ha, hb]

theorem measurement_krausMap (label : I → J) (M : Matrix I I ℂ) :
    Cloning.Channels.krausMap (measurementKraus label) M = measuredMatrix label M := by
  ext a b
  simp only [Cloning.Channels.krausMap, Matrix.sum_apply, measurementKraus_sandwich,
    measuredMatrix, Matrix.diagonal_apply]
  by_cases hab : a=b
  · subst b
    simp only [if_true, and_self]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a=label i <;> simp [hi, eq_comm]
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    have h : ¬(a=label i ∧ b=label i) := by rintro ⟨rfl,rfl⟩; exact hab rfl
    exact if_neg h

/-- An actual finite classical register measurement channel. -/
def measurementChannel (label : I → J) : QuantumChannel (Register I) (Register J) :=
  FiniteKrausLift.channel (measurementKraus label) (measurementKraus_normalization label)

theorem measurementChannel_registerLift (label : I → J) (M : Matrix I I ℂ) :
    (measurementChannel label).toLinearMap (registerLiftCLM M) = registerLiftCLM (measuredMatrix label M) := by
  rw [measurementChannel, FiniteKrausLift.channel_registerLiftCLM, measurement_krausMap]

theorem registerLift_matrixOf (A : TraceClass (Register I)) :
    registerLiftCLM (matrixOf (registerBasis I) A.1) = A := by
  change matrixLift (registerBasis I) (matrixOf (registerBasis I) A.1) = A
  simpa only [HilbertBasis.coe_toOrthonormalBasis] using
    Cloning.InfiniteFidelityHilbertSum.matrixLift_basis_matrixOf (registerBasis I).toOrthonormalBasis A

theorem measurementChannel_apply (label : I → J) (A : TraceClass (Register I)) :
    (measurementChannel label).toLinearMap A =
      registerLiftCLM (measuredMatrix label (matrixOf (registerBasis I) A.1)) := by
  conv_lhs => rw [← registerLift_matrixOf A]
  exact measurementChannel_registerLift label _

end Cloning.PCTCountMeasurement
