import Cloning.MatrixFidelitySymmetry
import Cloning.MatrixRegularization
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Optimal positive-definite witnesses for matrix fidelity

The geometric-mean witness is constructed explicitly. Its Riccati identity,
positive definiteness, trace objective, and positive block-matrix realization
are all proved from concrete matrix algebra.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix Cloning.MatrixRegularization
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The geometric-mean witness solving `H A H = B` for positive definite inputs. -/
def fidelityWitness (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt A)⁻¹ * CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A) * (CFC.sqrt A)⁻¹

/-- Congruence by the invertible positive square root preserves positive
 definiteness. -/
lemma fidelityWitness_middle_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (CFC.sqrt A * B * CFC.sqrt A).PosDef := by
  simpa only [sqrt_conjTranspose] using
    hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (sqrt_isUnit hA))

/-- The geometric-mean witness is positive definite. -/
theorem fidelityWitness_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (fidelityWitness A B).PosDef := by
  have hM := fidelityWitness_middle_posDef hA hB
  have hR : (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)).PosDef :=
    hM.isStrictlyPositive.sqrt.posDef
  simpa only [fidelityWitness, sqrt_inv_conjTranspose] using
    hR.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit (sqrt_inv_posDef hA).isUnit)

/-- The witness exactly solves the positive matrix Riccati equation. -/
theorem fidelityWitness_equation {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    fidelityWitness A B * A * fidelityWitness A B = B := by
  let S := CFC.sqrt A
  let R := CFC.sqrt (S * B * S)
  let K := S⁻¹
  have hKA : K * A * K = 1 := sqrt_inv_sandwich hA
  have hRS : R * R = S * B * S :=
    sqrt_mul_self (fidelityWitness_middle_posDef hA hB).posSemidef
  have hKS : K * S = 1 := sqrt_inv_mul hA
  have hSK : S * K = 1 := sqrt_mul_inv hA
  change (K * R * K) * A * (K * R * K) = B
  calc
    _ = K * R * (K * A * K) * R * K := by simp only [Matrix.mul_assoc]
    _ = K * (R * R) * K := by rw [hKA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = K * (S * B * S) * K := by rw [hRS]
    _ = (K * S) * B * (S * K) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [hKS, hSK, Matrix.one_mul, Matrix.mul_one]

/-- The trace pairing with the geometric-mean witness is exactly root fidelity. -/
theorem fidelityWitness_trace {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (Matrix.trace (A * fidelityWitness A B)).re = fidelity A B := by
  have hcyc : Matrix.trace (A * fidelityWitness A B) =
      Matrix.trace (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)) := by
    unfold fidelityWitness
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rw [← Matrix.mul_assoc, sqrt_inv_sandwich hA, Matrix.one_mul]
  rw [hcyc, fidelity_symm hA.posSemidef hB.posSemidef]
  rfl

/-- An optimal positive definite witness, with its exact objective and equation. -/
theorem exists_fidelity_witness {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ H : Matrix n n ℂ, H.PosDef ∧ H * A * H = B ∧
      (Matrix.trace (A * H)).re = fidelity A B :=
  ⟨fidelityWitness A B, fidelityWitness_posDef hA hB,
    fidelityWitness_equation hA hB, fidelityWitness_trace hA hB⟩

/-- A Hermitian Riccati solution gives a positive block matrix by rectangular
congruence of `A` with the vertical matrix `[I;H]`. -/
lemma riccati_block_posSemidef {A B H : Matrix n n ℂ}
    (hA : A.PosSemidef) (hH : H.IsHermitian) (hHAH : H * A * H = B) :
    (Matrix.fromBlocks A (A * H) (A * H).conjTranspose B).PosSemidef := by
  have hp := hA.mul_mul_conjTranspose_same (Matrix.fromRows (1 : Matrix n n ℂ) H)
  simpa only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one, Matrix.fromRows_mul, Matrix.mul_fromCols,
    Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromCols_fromRows_eq_fromBlocks,
    Matrix.one_mul, Matrix.mul_one, hH.eq, hHAH, Matrix.conjTranspose_mul,
    hA.isHermitian.eq] using hp

/-- A feasible fidelity SDP block attaining the exact trace objective, for
positive definite input matrices. -/
theorem exists_fidelity_block_witness {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ X : Matrix n n ℂ, (Matrix.fromBlocks A X X.conjTranspose B).PosSemidef ∧
      (Matrix.trace X).re = fidelity A B := by
  obtain ⟨H, hH, hHAH, htrace⟩ := exists_fidelity_witness hA hB
  exact ⟨A * H, riccati_block_posSemidef hA.posSemidef hH.isHermitian hHAH, htrace⟩

end Cloning.MatrixFidelity
