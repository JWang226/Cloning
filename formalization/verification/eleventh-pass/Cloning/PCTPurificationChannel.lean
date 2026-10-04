import Cloning.CartanChannel
import Cloning.MatrixFidelityBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite-matrix square-root purification channels

The square-root construction of Girardi--Mele--Lami is a genuine completely
positive trace-preserving map whenever its positive moment operator has identity
partial trace. This file builds the Kraus matrices and proves their normalization.
The moment operators below are constructed from maximally entangled tensor
vectors; their normalization is derived from the unitarity of the sampled
matrices, rather than assumed as a channel axiom.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace Cloning.PCTPurificationChannel

open Cloning.Channels Cloning.CartanChannel Cloning.Compression Cloning.MatrixFidelity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

local instance matrixCStar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- Square-root sandwich on the input with an unnormalised identity ancilla. -/
def purificationMap (R : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :=
  CFC.sqrt R * (X ⊗ₖ (1 : Matrix B B ℂ)) * CFC.sqrt R

/-- The environment-indexed Kraus matrices of the square-root sandwich. -/
def purificationKraus (R : Matrix (A × B) (A × B) ℂ) :
    B → Matrix (A × B) A ℂ :=
  sliceKraus (CFC.sqrt R)

theorem purificationMap_eq_kraus (R : Matrix (A × B) (A × B) ℂ)
    (X : Matrix A A ℂ) :
    purificationMap R X = krausMap (purificationKraus R) X := by
  simpa only [purificationMap, purificationKraus, sqrt_conjTranspose] using
    core_eq_kraus (CFC.sqrt R) X

theorem purificationKraus_normalization {R : Matrix (A × B) (A × B) ℂ}
    (hR : R.PosSemidef) :
    (∑ b, (purificationKraus R b)ᴴ * purificationKraus R b) = partialTrace R := by
  rw [purificationKraus, slice_normalization, sqrt_conjTranspose, sqrt_mul_self hR]

/-- Concrete CPTP map, with Kraus positivity checked at every matrix level. -/
def purificationChannel (R : Matrix (A × B) (A × B) ℂ)
    (hR : R.PosSemidef) (hnorm : partialTrace R = 1) : MatrixChannel A (A × B) :=
  ofKraus (purificationKraus R) ((purificationKraus_normalization hR).trans hnorm)

theorem purificationChannel_apply (R : Matrix (A × B) (A × B) ℂ)
    (hR : R.PosSemidef) (hnorm : partialTrace R = 1) (X : Matrix A A ℂ) :
    (purificationChannel R hR hnorm).toFun X = purificationMap R X :=
  (purificationMap_eq_kraus R X).symm

/-- Tensor power matrix, in the actual computational word basis. -/
def tensorPower (n : ℕ) (X : Matrix A B ℂ) :
    Matrix (Fin n → A) (Fin n → B) ℂ :=
  fun a b => ∏ i, X (a i) (b i)

theorem tensorPower_mul {C : Type*} [Fintype C]
    (n : ℕ) (X : Matrix A B ℂ) (Y : Matrix B C ℂ) :
    tensorPower n (X * Y) = tensorPower n X * tensorPower n Y := by
  ext a c
  simp only [tensorPower, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i b => X (a i) b * Y b (c i))

theorem tensorPower_star (n : ℕ) (X : Matrix A B ℂ) :
    tensorPower n Xᴴ = (tensorPower n X)ᴴ := by
  ext a b
  simp [tensorPower, Matrix.conjTranspose_apply]

@[simp] theorem tensorPower_one (n : ℕ) :
    tensorPower n (1 : Matrix A A ℂ) = 1 := by
  classical
  ext a b
  simp only [tensorPower, Matrix.one_apply]
  by_cases h : a = b
  · subst b
    simp
  · have hi : ∃ i, a i ≠ b i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

/-- Vectorisation of a sampled unitary tensor power. -/
def entangledTensor (n : ℕ) (U : Matrix A A ℂ) :
    (Fin n → A) × (Fin n → A) → ℂ :=
  fun ab => tensorPower n U ab.1 ab.2

/-- Rank-one matrix of the unnormalised entangled tensor vector. -/
def entangledMoment (n : ℕ) (U : Matrix A A ℂ) :
    Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ :=
  fun ab cd => entangledTensor n U ab * star (entangledTensor n U cd)

theorem entangledMoment_posSemidef (n : ℕ) (U : Matrix A A ℂ) :
    (entangledMoment n U).PosSemidef := by
  simpa only [entangledMoment, Matrix.vecMulVec_apply] using
    Matrix.posSemidef_vecMulVec_self_star (entangledTensor n U)

theorem partialTrace_entangledMoment (n : ℕ) (U : Matrix A A ℂ)
    (hU : Uᴴ * U = 1) : partialTrace (entangledMoment n U) = 1 := by
  have hUn : tensorPower n U * (tensorPower n U)ᴴ = 1 := by
    rw [← tensorPower_star, ← tensorPower_mul, mul_eq_one_comm.mp hU, tensorPower_one]
  ext a c
  simpa [partialTrace, entangledMoment, entangledTensor, Matrix.mul_apply,
    Matrix.conjTranspose_apply] using congrArg (fun M => M a c) hUn

/-- Finite randomized entangled moment, for arbitrary sampled unitaries. -/
def finiteMoment {ι : Type*} [Fintype ι] (n : ℕ) (w : ι → ℝ)
    (U : ι → Matrix A A ℂ) :=
  ∑ i, w i • entangledMoment n (U i)

theorem finiteMoment_posSemidef {ι : Type*} [Fintype ι] (n : ℕ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → Matrix A A ℂ) :
    (finiteMoment n w U).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (entangledMoment_posSemidef n (U i)).smul (hw i)

theorem partialTrace_finiteMoment {ι : Type*} [Fintype ι] (n : ℕ)
    (w : ι → ℝ) (hw : ∑ i, w i = 1) (U : ι → Matrix A A ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) :
    partialTrace (finiteMoment n w U) = 1 := by
  have hpartial : partialTrace (finiteMoment n w U) =
      ∑ i, w i • partialTrace (entangledMoment n (U i)) := by
    ext a c
    simp only [partialTrace, finiteMoment, Matrix.sum_apply, Matrix.smul_apply,
      Finset.smul_sum]
    exact Finset.sum_comm
  rw [hpartial]
  simp only [partialTrace_entangledMoment n _ (hU _), ← Finset.sum_smul, hw, one_smul]

/-- A channel whose moment is constructed directly from finitely sampled
unitaries; no positivity or trace-balance premise remains. -/
def finitePurificationChannel {ι : Type*} [Fintype ι] (n : ℕ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (U : ι → Matrix A A ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1) :
    MatrixChannel (Fin n → A) ((Fin n → A) × (Fin n → A)) :=
  purificationChannel (finiteMoment n w U) (finiteMoment_posSemidef n w hw U)
    (partialTrace_finiteMoment n w hsum U hU)

/-- If the moment commutes with a square-root input, the channel sandwich
equals the sandwich that purifies that input. -/
theorem purificationMap_square {R : Matrix (A × B) (A × B) ℂ}
    (hR : R.PosSemidef) (S : Matrix A A ℂ)
    (hcomm : Commute R (S ⊗ₖ (1 : Matrix B B ℂ))) :
    purificationMap R (S * S) =
      (S ⊗ₖ (1 : Matrix B B ℂ)) * R * (S ⊗ₖ (1 : Matrix B B ℂ)) := by
  have hs : Commute (CFC.sqrt R) (S ⊗ₖ (1 : Matrix B B ℂ)) :=
    hcomm.cfcₙ_nnreal NNReal.sqrt
  have hten : (S * S) ⊗ₖ (1 : Matrix B B ℂ) =
      (S ⊗ₖ (1 : Matrix B B ℂ)) * (S ⊗ₖ (1 : Matrix B B ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [purificationMap, hten, ← Matrix.mul_assoc, hs.eq]
  calc
    _ = (S ⊗ₖ (1 : Matrix B B ℂ)) *
        (CFC.sqrt R * (S ⊗ₖ (1 : Matrix B B ℂ))) * CFC.sqrt R := by
      simp only [Matrix.mul_assoc]
    _ = (S ⊗ₖ (1 : Matrix B B ℂ)) *
        ((S ⊗ₖ (1 : Matrix B B ℂ)) * CFC.sqrt R) * CFC.sqrt R := by rw [hs.eq]
    _ = (S ⊗ₖ (1 : Matrix B B ℂ)) *
        (S ⊗ₖ (1 : Matrix B B ℂ)) * R := by
      simp only [Matrix.mul_assoc, sqrt_mul_self hR]
    _ = _ := by
      rw [Matrix.mul_assoc, ← hcomm.eq, ← Matrix.mul_assoc, ← hcomm.eq]

/-- Bochner moment of the physical maximally entangled tensor projectors. -/
def integralMoment {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Measure Ω) (U : Ω → Matrix A A ℂ) :=
  ∫ t, entangledMoment n (U t) ∂μ

theorem integralMoment_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Measure Ω) (U : Ω → Matrix A A ℂ) :
    (integralMoment n μ U).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact integral_nonneg (fun t => (entangledMoment_posSemidef n (U t)).nonneg)

/-- The actual matrix partial trace, bundled as a continuous linear map. -/
def partialTraceCLM : Matrix (A × B) (A × B) ℂ →L[ℂ] Matrix A A ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := partialTrace
      map_add' := by intros; ext a c; simp [partialTrace, Finset.sum_add_distrib]
      map_smul' := by intros; ext a c; simp [partialTrace, Finset.mul_sum] }

theorem partialTrace_integralMoment {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → Matrix A A ℂ)
    (hU : ∀ t, (U t)ᴴ * U t = 1)
    (hi : Integrable (fun t => entangledMoment n (U t)) μ) :
    partialTrace (integralMoment n μ U) = 1 := by
  have h := (partialTraceCLM (A := Fin n → A) (B := Fin n → A)).integral_comp_comm hi |>.symm
  change partialTrace (integralMoment n μ U) =
    ∫ t, partialTrace (entangledMoment n (U t)) ∂μ at h
  rw [h]
  simp only [partialTrace_entangledMoment n _ (hU _), integral_const, probReal_univ,
    one_smul]

/-- The Bochner version, including Haar distributions once their ordinary
integrability is established. Its channel laws follow from actual unitary
matrix entries and the total probability mass. -/
def integralPurificationChannel {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → Matrix A A ℂ)
    (hU : ∀ t, (U t)ᴴ * U t = 1)
    (hi : Integrable (fun t => entangledMoment n (U t)) μ) :
    MatrixChannel (Fin n → A) ((Fin n → A) × (Fin n → A)) :=
  purificationChannel (integralMoment n μ U) (integralMoment_posSemidef n μ U)
    (partialTrace_integralMoment n μ U hU hi)

end Cloning.PCTPurificationChannel
