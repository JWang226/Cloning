import Cloning.TensorWeylMatrixSupport

/-! Finite cutoff oscillator matrix powers are the literal Fock ladder powers. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem inner_numberBasis_numberVector {D : ℕ} (k : Fin D → ℕ) (c : NumberCoefficients D) :
    ⟪numberBasis D k, numberVector c⟫_ℂ = c k := by
  simp only [numberVector, Finsupp.linearCombination_apply, Finsupp.sum,
    inner_sum, inner_smul_right, orthonormal_iff_ite.mp (numberBasis D).orthonormal]
  by_cases hk : k ∈ c.support
  · simp [hk]
  · have hz := Finsupp.notMem_support_iff.mp hk
    simp [hk, hz]

def cutoffNumberOccupation (d Q : ℕ) (i : CutoffIndex d Q) :=
  fockOccupation d (cutoffOccupation d Q i).val

theorem cutoffNumberOccupation_injective (d Q : ℕ) :
    Function.Injective (cutoffNumberOccupation d Q) := by
  intro i j h
  apply (cutoffOccupation d Q).injective
  exact Subtype.ext (fockOccupation_injective d h)

theorem wordFockOccupation_cutoffWord (Q : ℕ) (i : CutoffIndex d Q) :
    wordFockOccupation (cutoffWord d Q i) = cutoffNumberOccupation d Q i := by
  unfold wordFockOccupation cutoffWord cutoffNumberOccupation
  congr 1
  funext a
  exact canonicalWord_count (cutoffOccupation d Q i).val a

def numberCoordinates (Q : ℕ) (c : NumberCoefficients (Fintype.card (PositiveRoot d))) :
    CutoffIndex d Q → ℂ := fun i => c (cutoffNumberOccupation d Q i)

theorem numberCoefficients_eq_cutoff_sum (Q : ℕ)
    (c : NumberCoefficients (Fintype.card (PositiveRoot d))) (hc : c ∈ numberHeightCutoff d Q) :
    c = ∑ i : CutoffIndex d Q,
      numberCoordinates Q c i • Finsupp.single (cutoffNumberOccupation d Q i) 1 := by
  classical
  ext k
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
    numberCoordinates]
  by_cases hk : rootNumberHeight d k ≤ Q
  · obtain ⟨i, hi⟩ := exists_cutoffNumberOccupation k hk
    change cutoffNumberOccupation d Q i = k at hi
    subst k
    simp only [mul_ite, mul_one, mul_zero]
    have he (j : CutoffIndex d Q) :
        cutoffNumberOccupation d Q j = cutoffNumberOccupation d Q i ↔ j = i :=
      (cutoffNumberOccupation_injective d Q).eq_iff
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · have hz : c k = 0 := (Finsupp.mem_supported' ℂ c).mp hc k hk
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hi : cutoffNumberOccupation d Q i ≠ k := by
      intro hi
      apply hk
      rw [← hi]
      exact cutoffNumberOccupation_height Q i
    simp [hi]

theorem numberVector_eq_cutoff_sum (Q : ℕ)
    (c : NumberCoefficients (Fintype.card (PositiveRoot d))) (hc : c ∈ numberHeightCutoff d Q) :
    numberVector c = ∑ i : CutoffIndex d Q, numberCoordinates Q c i • cutoffNumberFrame d Q i := by
  have h := congrArg numberVector (numberCoefficients_eq_cutoff_sum Q c hc)
  simpa only [map_sum, map_smul, numberVector_single, one_smul,
    cutoffNumberFrame, cutoffNumberOccupation] using h

theorem numberGenerator_cutoff_single (Q : ℕ) (z : PositiveRoot d → ℂ)
    (i j : CutoffIndex d Q) :
    numberGenerator (rootFockAmplitude z) (Finsupp.single (cutoffNumberOccupation d Q j) 1)
      (cutoffNumberOccupation d Q i) = oscillatorCutoffMatrix Q z i j := by
  rw [← inner_numberBasis_numberVector, numberGenerator_single, one_smul,
    numberVector_ladderCoefficients, oscillatorCutoffMatrix_eq_numberLadder,
    wordFockOccupation_cutoffWord]
  rfl

theorem numberCoordinates_generator (Q : ℕ) (z : PositiveRoot d → ℂ)
    (c : NumberCoefficients (Fintype.card (PositiveRoot d))) (hc : c ∈ numberHeightCutoff d Q) :
    numberCoordinates Q (numberGenerator (rootFockAmplitude z) c) =
      (oscillatorCutoffMatrix Q z).mulVec (numberCoordinates Q c) := by
  have h := congrArg (numberGenerator (rootFockAmplitude z))
    (numberCoefficients_eq_cutoff_sum Q c hc)
  funext i
  change numberGenerator (rootFockAmplitude z) c (cutoffNumberOccupation d Q i) = _
  rw [h]
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    numberGenerator_cutoff_single, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem numberCoordinates_iterate (Q R : ℕ) (z : PositiveRoot d → ℂ)
    (c : NumberCoefficients (Fintype.card (PositiveRoot d))) (hc : c ∈ numberHeightCutoff d R) :
    ∀ m : ℕ, R+m*d ≤ Q →
      numberCoordinates Q (numberIterate (rootFockAmplitude z) c m) =
        ((oscillatorCutoffMatrix Q z)^m).mulVec (numberCoordinates Q c) := by
  intro m
  induction m with
  | zero => intro _; simp [numberIterate_zero]
  | succ m ih =>
    intro hQ
    have hm : R+m*d ≤ Q := (Nat.add_le_add_left
      (Nat.mul_le_mul_right d (Nat.le_succ m)) R).trans hQ
    rw [numberIterate_succ, numberCoordinates_generator Q z _
      (numberHeightCutoff_mono hm (numberIterate_mem z c hc m)), ih hm,
      pow_succ', Matrix.mulVec_mulVec]

theorem numberCoordinates_word (Q : ℕ) (w : List (PositiveRoot d)) :
    numberCoordinates Q (Finsupp.single (wordFockOccupation w) 1) = limitingWordCoordinates Q w := by
  funext i
  simp only [numberCoordinates, Finsupp.single_apply, limitingWordCoordinates,
    ← wordFockOccupation_cutoffWord, wordFockOccupation_eq_iff]
  by_cases h : w.Perm (cutoffWord d Q i)
  · simp [h, h.symm]
  · have hh : ¬ (cutoffWord d Q i).Perm w := fun h' => h h'.symm
    simp [h, hh]

/-- All intermediate ladder states fit into the chosen height cutoff. Hence
the finite oscillator matrix power equals the actual infinite-Fock vector. -/
theorem oscillatorCutoffMatrix_power_eq_numberPower
    (Q m : ℕ) (z : PositiveRoot d → ℂ) (w : List (PositiveRoot d))
    (hQ : loweringHeight w+m*d ≤ Q) :
    (∑ i : CutoffIndex d Q,
      (((oscillatorCutoffMatrix Q z)^m).mulVec (limitingWordCoordinates Q w) i) •
        cutoffNumberFrame d Q i) =
      numberPower (rootFockAmplitude z) (wordFockOccupation w) m := by
  rw [← numberCoordinates_word, ← numberCoordinates_iterate Q (loweringHeight w) z _
    (wordCoefficients_mem w) m hQ]
  exact (numberVector_eq_cutoff_sum Q _
    (numberHeightCutoff_mono hQ (numberIterate_mem z _ (wordCoefficients_mem w) m))).symm

end Cloning.TensorLocalUnitary
