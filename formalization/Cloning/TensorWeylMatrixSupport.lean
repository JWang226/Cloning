import Cloning.TensorWeylMatrixEntries
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Exact finite root-height support of literal oscillator powers. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def rootNumberOccupation (d : ℕ) (k : Fin (Fintype.card (PositiveRoot d)) → ℕ) :
    PositiveRoot d → ℕ := fun a => k ((Fintype.equivFin (PositiveRoot d)) a)

@[simp] theorem fockOccupation_rootNumberOccupation
    (k : Fin (Fintype.card (PositiveRoot d)) → ℕ) :
    fockOccupation d (rootNumberOccupation d k) = k := by
  funext i
  simp [fockOccupation, rootNumberOccupation]

@[simp] theorem rootNumberOccupation_fockOccupation (k : PositiveRoot d → ℕ) :
    rootNumberOccupation d (fockOccupation d k) = k := by
  funext a
  simp [fockOccupation, rootNumberOccupation]

def rootNumberHeight (d : ℕ) (k : Fin (Fintype.card (PositiveRoot d)) → ℕ) : ℕ :=
  occupationHeight (rootNumberOccupation d k)

theorem rootNumberHeight_word (w : List (PositiveRoot d)) :
    rootNumberHeight d (wordFockOccupation w) = loweringHeight w := by
  rw [rootNumberHeight, wordFockOccupation, rootNumberOccupation_fockOccupation]
  exact (loweringHeight_eq_sum_count w).symm

theorem rootNumberHeight_update_le (k : Fin (Fintype.card (PositiveRoot d)) → ℕ)
    (i : Fin (Fintype.card (PositiveRoot d))) (l : ℕ) (hl : l ≤ k i+1) :
    rootNumberHeight d (Function.update k i l) ≤ rootNumberHeight d k + d := by
  let a := (Fintype.equivFin (PositiveRoot d)).symm i
  have hroot : a.height ≤ d := by
    have hd := a.val.2.isLt
    dsimp [PositiveRoot.height]
    omega
  unfold rootNumberHeight occupationHeight rootNumberOccupation
  calc
    _ ≤ ∑ b : PositiveRoot d,
        (b.height * k ((Fintype.equivFin (PositiveRoot d)) b) +
          if b = a then a.height else 0) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hba : b = a
      · subst b
        simpa [a, Function.update, Nat.mul_add] using Nat.mul_le_mul_left a.height hl
      · have hi : (Fintype.equivFin (PositiveRoot d)) b ≠ i := by
          intro h
          apply hba
          exact (Equiv.apply_eq_iff_eq_symm_apply _).mp h
        simp [Function.update_of_ne hi, hba]
    _ = (∑ b : PositiveRoot d, b.height * k ((Fintype.equivFin (PositiveRoot d)) b)) + a.height := by
      simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left hroot _

def numberHeightCutoff (d R : ℕ) : Submodule ℂ (NumberCoefficients (Fintype.card (PositiveRoot d))) :=
  Finsupp.supported ℂ ℂ {k | rootNumberHeight d k ≤ R}

theorem numberHeightCutoff_mono {R Q : ℕ} (h : R ≤ Q) :
    numberHeightCutoff d R ≤ numberHeightCutoff d Q := by
  intro c hc k hk
  exact (hc hk).trans h

theorem numberLadderCoefficients_mem (z : PositiveRoot d → ℂ)
    (k : Fin (Fintype.card (PositiveRoot d)) → ℕ) {R : ℕ}
    (hk : rootNumberHeight d k ≤ R) :
    numberLadderCoefficients (rootFockAmplitude z) k ∈ numberHeightCutoff d (R+d) := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sub_mem
  · exact Finsupp.single_mem_supported ℂ _
      ((rootNumberHeight_update_le k i (k i+1) le_rfl).trans (Nat.add_le_add_right hk d))
  · exact Finsupp.single_mem_supported ℂ _
      ((rootNumberHeight_update_le k i (k i-1) (by omega)).trans (Nat.add_le_add_right hk d))

theorem numberGenerator_mem (z : PositiveRoot d → ℂ) {R : ℕ}
    (c : NumberCoefficients (Fintype.card (PositiveRoot d)))
    (hc : c ∈ numberHeightCutoff d R) :
    numberGenerator (rootFockAmplitude z) c ∈ numberHeightCutoff d (R+d) := by
  rw [numberGenerator, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (numberLadderCoefficients_mem z k (hc hk))

theorem numberIterate_mem (z : PositiveRoot d → ℂ) {R : ℕ}
    (c : NumberCoefficients (Fintype.card (PositiveRoot d)))
    (hc : c ∈ numberHeightCutoff d R) (m : ℕ) :
    numberIterate (rootFockAmplitude z) c m ∈ numberHeightCutoff d (R+m*d) := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    simpa only [numberIterate_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      numberGenerator_mem z _ ih

theorem wordCoefficients_mem (w : List (PositiveRoot d)) :
    Finsupp.single (wordFockOccupation w) (1 : ℂ) ∈
      numberHeightCutoff d (loweringHeight w) := by
  exact Finsupp.single_mem_supported ℂ _ (rootNumberHeight_word w).le

theorem cutoffNumberOccupation_height (Q : ℕ) (i : CutoffIndex d Q) :
    rootNumberHeight d (fockOccupation d (cutoffOccupation d Q i).val) ≤ Q := by
  rw [rootNumberHeight, rootNumberOccupation_fockOccupation]
  exact (cutoffOccupation d Q i).property

theorem exists_cutoffNumberOccupation {Q : ℕ}
    (k : Fin (Fintype.card (PositiveRoot d)) → ℕ) (hk : rootNumberHeight d k ≤ Q) :
    ∃ i : CutoffIndex d Q, fockOccupation d (cutoffOccupation d Q i).val = k := by
  refine ⟨(cutoffOccupation d Q).symm ⟨rootNumberOccupation d k, hk⟩, ?_⟩
  simp only [Equiv.apply_symm_apply, fockOccupation_rootNumberOccupation]

end Cloning.TensorLocalUnitary
