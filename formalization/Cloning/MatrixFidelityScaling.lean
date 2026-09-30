import Cloning.MatrixFidelity
import Cloning.BlockFidelity

/-!
# Scaling and diagonal specialization of matrix root fidelity

All square roots below are the continuous-functional-calculus square roots
of actual complex matrices. No abstract fidelity laws are assumed.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive matrix square root scales by the scalar square root. -/
theorem sqrt_smul_real (a : ℝ) (A : Matrix n n ℂ)
    (ha : 0 ≤ a) (hA : A.PosSemidef) :
    CFC.sqrt (a • A) = Real.sqrt a • CFC.sqrt A := by
  apply CFC.sqrt_unique
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt ha, sqrt_mul_self hA]
  · exact ((sqrt_posSemidef A).smul (Real.sqrt_nonneg a)).nonneg

/-- Positive scalar homogeneity in the first matrix argument. -/
theorem fidelity_smul_left (a : ℝ) (A B : Matrix n n ℂ)
    (ha : 0 ≤ a) (hA : A.PosSemidef) :
    fidelity (a • A) B = Real.sqrt a * fidelity A B := by
  unfold fidelity
  rw [mul_smul_comm, smul_mul_assoc,
    sqrt_smul_real a _ ha (sandwich_posSemidef hA B), Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]

/-- Positive scalar homogeneity in the second matrix argument. -/
theorem fidelity_smul_right (b : ℝ) (A B : Matrix n n ℂ)
    (hb : 0 ≤ b) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A (b • B) = Real.sqrt b * fidelity A B := by
  unfold fidelity
  rw [sqrt_smul_real b B hb hB]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, Real.mul_self_sqrt hb,
    sqrt_smul_real b _ hb (sandwich_posSemidef hA B), Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]

/-- Matrix root fidelity is homogeneous of degree one-half in each argument. -/
theorem fidelity_smul (a b : ℝ) (A B : Matrix n n ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity (a • A) (b • B) = Real.sqrt a * Real.sqrt b * fidelity A B := by
  rw [fidelity_smul_left a A (b • B) ha hA, fidelity_smul_right b A B hb hA hB]
  ring

/-- Square roots of nonnegative real diagonal matrices are entrywise square roots. -/
theorem sqrt_diagonal_real (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    CFC.sqrt (Matrix.diagonal fun i ↦ (p i : ℂ)) =
      Matrix.diagonal fun i ↦ (Real.sqrt (p i) : ℂ) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]
  · apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg (p i), rfl⟩

/-- For diagonal density matrices, quantum root fidelity is the classical
Hellinger affinity. The statement also holds for unnormalized nonnegative weights. -/
theorem fidelity_diagonal_real (p q : n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    fidelity (Matrix.diagonal fun i ↦ (p i : ℂ))
      (Matrix.diagonal fun i ↦ (q i : ℂ)) =
      Cloning.BlockFidelity.classicalAffinity p q := by
  unfold fidelity
  rw [sqrt_diagonal_real q hq]
  simp only [Matrix.diagonal_mul_diagonal]
  have hdiag : (Matrix.diagonal fun i ↦
      (Real.sqrt (q i) : ℂ) * (p i : ℂ) * (Real.sqrt (q i) : ℂ)) =
      Matrix.diagonal fun i ↦ ((p i * q i : ℝ) : ℂ) := by
    congr 1
    funext i
    calc
      (Real.sqrt (q i) : ℂ) * (p i : ℂ) * (Real.sqrt (q i) : ℂ) =
          (p i : ℂ) * ((Real.sqrt (q i) : ℂ) * (Real.sqrt (q i) : ℂ)) := by ring
      _ = ((p i * q i : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hq i), Complex.ofReal_mul]
  rw [hdiag, sqrt_diagonal_real (fun i ↦ p i * q i) (fun i ↦ mul_nonneg (hp i) (hq i)),
    Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re, Cloning.BlockFidelity.classicalAffinity]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.sqrt_mul (hp i) (q i)

end Cloning.MatrixFidelity
