import Cloning.MatrixFidelity
import Cloning.MatrixFidelityProjector
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Concavity and finite mixtures for concrete matrix fidelity

Operator concavity of the positive square root is proved from a matrix variance
identity and operator monotonicity. No concavity law is assumed.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance matrixMixturesCStarAlgebra : CStarAlgebra (Matrix n n ℂ) where

/-- The binary matrix variance identity; the matrices need not commute. -/
lemma weighted_square_gap (U V : Matrix n n ℂ) (a b : ℝ) (hab : a + b = 1) :
    a • (U * U) + b • (V * V) - (a • U + b • V) * (a • U + b • V) =
      (a * b) • ((U - V) * (U - V)) := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    smul_mul_assoc, mul_smul_comm]
  module

/-- Operator concavity of the positive square root, proved by the variance
identity and monotonicity of the square root. -/
theorem sqrt_operator_concave {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • CFC.sqrt A + b • CFC.sqrt B ≤ CFC.sqrt (a • A + b • B) := by
  let H := a • CFC.sqrt A + b • CFC.sqrt B
  let D := CFC.sqrt A - CFC.sqrt B
  have hH : H.PosSemidef :=
    ((sqrt_posSemidef A).smul ha).add ((sqrt_posSemidef B).smul hb)
  have hD : D.conjTranspose = D := by
    simp only [D, Matrix.conjTranspose_sub, sqrt_conjTranspose]
  have hDD : (D * D).PosSemidef := by
    simpa only [hD] using Matrix.posSemidef_conjTranspose_mul_self D
  have hgap : a • A + b • B - H * H = (a * b) • (D * D) := by
    simpa only [H, D, sqrt_mul_self hA, sqrt_mul_self hB] using
      weighted_square_gap (CFC.sqrt A) (CFC.sqrt B) a b hab
  have hle : H * H ≤ a • A + b • B := by
    change (a • A + b • B - H * H).PosSemidef
    rw [hgap]
    exact hDD.smul (mul_nonneg ha hb)
  have h := CFC.sqrt_le_sqrt (H * H) (a • A + b • B) hle
  rw [CFC.sqrt_mul_self H hH.nonneg] at h
  exact h

/-- Root fidelity is concave in its first positive matrix argument, with a
fixed target matrix. -/
theorem fidelity_concave_left {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (T : Matrix n n ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * fidelity A T + b * fidelity B T ≤ fidelity (a • A + b • B) T := by
  have h := trace_re_mono (sqrt_operator_concave
    (sandwich_posSemidef hA T) (sandwich_posSemidef hB T) a b ha hb hab)
  have hs : CFC.sqrt T * (a • A + b • B) * CFC.sqrt T =
      a • (CFC.sqrt T * A * CFC.sqrt T) + b • (CFC.sqrt T * B * CFC.sqrt T) := by
    simp only [Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc]
  unfold fidelity
  rw [hs]
  simpa only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.smul_re, smul_eq_mul] using h

omit [Fintype n] [DecidableEq n] in
/-- The cone of positive semidefinite matrices is convex over the reals. -/
lemma convex_posSemidef_matrices :
    Convex ℝ {A : Matrix n n ℂ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

/-- Concavity on the full positive cone in the standard Mathlib sense. -/
theorem concaveOn_fidelity_left (T : Matrix n n ℂ) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosSemidef} (fun A => fidelity A T) := by
  refine ⟨convex_posSemidef_matrices, ?_⟩
  intro A hA B hB a b ha hb hab
  exact fidelity_concave_left hA hB T a b ha hb hab

/-- Mixing positive sector states does not decrease fidelity below the
corresponding mixture of their individual fidelities. -/
theorem fidelity_finite_mixture {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (T : Matrix n n ℂ) (w : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∑ i, w i * fidelity (A i) T ≤ fidelity (∑ i, w i • A i) T := by
  exact (concaveOn_fidelity_left T).le_map_sum
    (fun i _ => hw i) hsum (fun i _ => hA i)

/-- A uniform lower sector-fidelity bound survives arbitrary finite probability
mixtures; no choice of a particular input sector is needed. -/
theorem fidelity_finite_mixture_lower {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (T : Matrix n n ℂ) (w : ι → ℝ) (c : ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hc : ∀ i, 0 < w i → c ≤ fidelity (A i) T) :
    c ≤ fidelity (∑ i, w i • A i) T := by
  calc
    c = ∑ i, w i * c := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, w i * fidelity (A i) T := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hpos : 0 < w i
      · exact mul_le_mul_of_nonneg_left (hc i hpos) (hw i)
      · have hz : w i = 0 := le_antisymm (le_of_not_gt hpos) (hw i)
        simp only [hz, zero_mul, le_refl]
    _ ≤ _ := fidelity_finite_mixture A T w hA hw hsum

end Cloning.MatrixFidelity
