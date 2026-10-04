import Cloning.PCTPurificationChannelPhysical

/-! Actual symmetric support of the Haar square-root purification channel,
for every complex input matrix. -/
noncomputable section
open scoped BigOperators Matrix Kronecker MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Matrix MeasureTheory Cloning.InfiniteTraceClass Cloning.PCT
open Cloning.PCTPurificationChannel Cloning.InfiniteFiniteCorner

namespace Cloning.PurificationSupport
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance registerFiniteDimensional (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

local instance matrixCStar (I : Type*) [Fintype I] [DecidableEq I] :
    CStarAlgebra (Matrix I I ℂ) where

/-- Simultaneous slot permutations in the grouped system/environment register. -/
def groupedSymmetric (n : ℕ) : Submodule ℂ (Register ((Fin n → A) × (Fin n → A))) where
  carrier := {x | ∀ a b (σ : Equiv.Perm (Fin n)), x (a ∘ σ, b ∘ σ) = x (a, b)}
  zero_mem' := by intro a b σ; rfl
  add_mem' := by intro x y hx hy a b σ; exact congrArg₂ (· + ·) (hx a b σ) (hy a b σ)
  smul_mem' := by intro c x hx a b σ; exact congrArg (c • ·) (hx a b σ)

/-- This subspace is exactly the regrouped physical symmetric subspace. -/
theorem regroup_mem_groupedSymmetric_iff (n : ℕ) (x : Register (Fin n → A × A)) :
    regroup n x ∈ groupedSymmetric (A := A) n ↔ x ∈ physicalSymmetric n := by
  constructor
  · intro hx w σ
    simpa only [regroup_apply, Function.comp_apply, Prod.eta] using
      hx (fun i => (w i).1) (fun i => (w i).2) σ
  · intro hx a b σ
    simpa only [regroup_apply, Function.comp_apply] using hx (fun i => (a i, b i)) σ

/-- Computational matrix of the actual orthogonal symmetric projection. -/
def symmetricMatrix (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ :=
  matrixOf (registerBasis _) (groupedSymmetric (A := A) n).starProjection

theorem ofMatrix_injective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (ofMatrix (registerBasis I)) := by
  intro X Y h
  have h' := congrArg (matrixOf (registerBasis I)) h
  simpa only [matrixOf_ofMatrix (registerBasis I).orthonormal] using h'

theorem ofMatrix_matrixOf_register {I : Type*} [Fintype I] [DecidableEq I]
    (T : Register I →L[ℂ] Register I) :
    ofMatrix (registerBasis I) (matrixOf (registerBasis I) T) = T := by
  apply register_operator_ext
  intro a b
  change (registerLiftCLM (matrixOf (registerBasis I) T)).1 (lp.single 2 b 1) a = _
  rw [registerLiftCLM_coefficient]
  simp only [matrixOf, registerBasis_apply, register_inner_single]

theorem ofMatrix_symmetricMatrix (n : ℕ) :
    ofMatrix (registerBasis _) (symmetricMatrix (A := A) n) =
      (groupedSymmetric (A := A) n).starProjection :=
  ofMatrix_matrixOf_register _

theorem symmetricMatrix_idempotent (n : ℕ) :
    symmetricMatrix (A := A) n * symmetricMatrix n = symmetricMatrix n := by
  apply ofMatrix_injective
  rw [ofMatrix_mul (registerBasis _).orthonormal, ofMatrix_symmetricMatrix]
  exact (isStarProjection_starProjection (U := groupedSymmetric (A := A) n)).isIdempotentElem.eq

theorem symmetricMatrix_conjTranspose (n : ℕ) :
    (symmetricMatrix (A := A) n).conjTranspose = symmetricMatrix n := by
  apply ofMatrix_injective
  rw [ofMatrix_conjTranspose, ofMatrix_symmetricMatrix]
  exact (isStarProjection_starProjection (U := groupedSymmetric (A := A) n)).isSelfAdjoint

/-- The actual grouped tensor coefficient vector of a bipartite matrix. -/
def momentVector (n : ℕ) (Z : Matrix A A ℂ) : Register ((Fin n → A) × (Fin n → A)) :=
  ⟨entangledTensor n Z, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

theorem momentVector_mem (n : ℕ) (Z : Matrix A A ℂ) :
    momentVector n Z ∈ groupedSymmetric n := by
  intro a b σ
  change (∏ i, Z (a (σ i)) (b (σ i))) = ∏ i, Z (a i) (b i)
  exact Equiv.prod_comp σ (fun i => Z (a i) (b i))

theorem symmetricMatrix_momentVector (n : ℕ) (Z : Matrix A A ℂ)
    (a : (Fin n → A) × (Fin n → A)) :
    ∑ b, symmetricMatrix (A := A) n a b * entangledTensor n Z b = entangledTensor n Z a := by
  have hv : (groupedSymmetric (A := A) n).starProjection (momentVector n Z) = momentVector n Z :=
    (groupedSymmetric (A := A) n).starProjection_eq_self_iff.mpr (momentVector_mem n Z)
  have he := inner_ofMatrix_apply (registerBasis _).orthonormal
    (symmetricMatrix (A := A) n) (momentVector n Z) a
  rw [ofMatrix_symmetricMatrix, hv] at he
  simpa only [registerBasis_apply, register_inner_single, momentVector] using he.symm

theorem entangledMoment_supported_left (n : ℕ) (Z : Matrix A A ℂ) :
    symmetricMatrix (A := A) n * entangledMoment n Z = entangledMoment n Z := by
  ext a c
  simp only [Matrix.mul_apply, entangledMoment, ← mul_assoc, ← Finset.sum_mul]
  rw [symmetricMatrix_momentVector]

theorem entangledMoment_supported_right (n : ℕ) (Z : Matrix A A ℂ) :
    entangledMoment n Z * symmetricMatrix (A := A) n = entangledMoment n Z := by
  have h := congrArg Matrix.conjTranspose (entangledMoment_supported_left n Z)
  simpa only [Matrix.conjTranspose_mul, symmetricMatrix_conjTranspose,
    (entangledMoment_posSemidef n Z).isHermitian.eq] using h

/-- Support of the actual Haar moment follows from its concrete tensor integrands. -/
theorem haarMoment_supported (n : ℕ) :
    symmetricMatrix (A := A) n * haarMoment n * symmetricMatrix n = haarMoment n := by
  have he := (matrixSandwichCLM (symmetricMatrix (A := A) n)).integral_comp_comm
    (integrable_haar_entangledMoment (A := A) n)
  change (∫ U : unitary (Matrix A A ℂ), symmetricMatrix n * entangledMoment n (U : Matrix A A ℂ) *
      (symmetricMatrix n).conjTranspose ∂unitaryHaar) =
    symmetricMatrix n * haarMoment n * (symmetricMatrix n).conjTranspose at he
  simpa only [symmetricMatrix_conjTranspose, entangledMoment_supported_left,
    entangledMoment_supported_right, haarMoment, integralMoment] using he.symm

/-- A positive matrix supported by an orthogonal projector has supported square root. -/
theorem sqrt_supported {I : Type*} [Fintype I] [DecidableEq I]
    (P R : Matrix I I ℂ) (hP : P * P = P) (hPs : P.conjTranspose = P)
    (hR : R.PosSemidef) (hPRP : P * R * P = R) :
    P * CFC.sqrt R = CFC.sqrt R ∧ CFC.sqrt R * P = CFC.sqrt R := by
  have hPR : P * R = R := by
    calc
      P * R = P * (P * R * P) := by rw [hPRP]
      _ = P * R * P := by simp only [← Matrix.mul_assoc, hP]
      _ = R := hPRP
  have hRP : R * P = R := by
    simpa only [Matrix.conjTranspose_mul, hPs, hR.isHermitian.eq] using
      congrArg Matrix.conjTranspose hPR
  have hzero : (CFC.sqrt R * (1 - P)).conjTranspose * (CFC.sqrt R * (1 - P)) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hPs, Cloning.MatrixFidelity.sqrt_conjTranspose]
    calc
      (1 - P) * CFC.sqrt R * (CFC.sqrt R * (1 - P)) =
          (1 - P) * (CFC.sqrt R * CFC.sqrt R) * (1 - P) := by simp only [Matrix.mul_assoc]
      _ = (1 - P) * R * (1 - P) := by rw [Cloning.MatrixFidelity.sqrt_mul_self hR]
      _ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPR, sub_self, Matrix.zero_mul]
  have hz : CFC.sqrt R * (1 - P) = 0 :=
    (CStarRing.star_mul_self_eq_zero_iff _).mp hzero
  have hright : CFC.sqrt R * P = CFC.sqrt R := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hz
    exact (sub_eq_zero.mp hz).symm
  refine ⟨?_, hright⟩
  simpa only [Matrix.conjTranspose_mul, hPs, Cloning.MatrixFidelity.sqrt_conjTranspose] using
    congrArg Matrix.conjTranspose hright

/-- No square-root support hypothesis is assumed for the Haar construction. -/
theorem haarMoment_sqrt_supported (n : ℕ) :
    symmetricMatrix (A := A) n * CFC.sqrt (haarMoment n) = CFC.sqrt (haarMoment n) ∧
      CFC.sqrt (haarMoment (A := A) n) * symmetricMatrix n = CFC.sqrt (haarMoment n) :=
  sqrt_supported (symmetricMatrix (A := A) n) (haarMoment (A := A) n)
    (symmetricMatrix_idempotent (A := A) n) (symmetricMatrix_conjTranspose (A := A) n)
    (haarMoment_posSemidef (A := A) n) (haarMoment_supported (A := A) n)

/-- The constructed Haar purification channel takes every complex matrix into
its actual physical symmetric sector, not only tensor-power density inputs. -/
theorem haarPurificationChannel_supported (n : ℕ)
    (X : Matrix (Fin n → A) (Fin n → A) ℂ) :
    symmetricMatrix (A := A) n * (haarPurificationChannel n).toFun X * symmetricMatrix n =
      (haarPurificationChannel n).toFun X := by
  rw [haarPurificationChannel_apply, purificationMap]
  obtain ⟨hleft, hright⟩ := haarMoment_sqrt_supported (A := A) n
  calc
    symmetricMatrix n * (CFC.sqrt (haarMoment n) * (X ⊗ₖ 1) * CFC.sqrt (haarMoment n)) *
        symmetricMatrix n =
      (symmetricMatrix n * CFC.sqrt (haarMoment n)) * (X ⊗ₖ 1) *
        (CFC.sqrt (haarMoment n) * symmetricMatrix n) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hleft, hright]


end Cloning.PurificationSupport
