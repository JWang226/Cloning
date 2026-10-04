import Cloning.WeylNumberTaylorLimit
import Cloning.TensorLocalUnitaryPolynomial
import Cloning.TensorLANEmbeddingPhysical
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Exact identification of the finite oscillator entries with actual Fock ladders. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem numberLadder_inner_skew (a : Fin d → ℂ) (k l : Fin d → ℕ) :
    ⟪numberLadder a k, numberBasis d l⟫_ℂ =
      -⟪numberBasis d k, numberLadder a l⟫_ℂ := by
  have h := (displacement_number_hasDerivAt a k 0).inner ℂ
    (displacement_number_hasDerivAt a l 0)
  have he (t : ℝ) :
      ⟪displacement (t • a) (numberBasis d k), displacement (t • a) (numberBasis d l)⟫_ℂ =
        ⟪numberBasis d k, numberBasis d l⟫_ℂ :=
    (weylUnitary (t • a)).inner_map_map _ _
  simp only [he, zero_smul, displacement_zero, ContinuousLinearMap.id_apply] at h
  have hz := h.unique (hasDerivAt_const 0 ⟪numberBasis d k, numberBasis d l⟫_ℂ)
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)

theorem number_lowering_entry (k l : Fin d → ℕ) (i : Fin d) :
    (Real.sqrt (k i : ℝ) : ℂ) * (if l = Function.update k i (k i-1) then 1 else 0) =
      (Real.sqrt (l i+1 : ℝ) : ℂ) * (if k = Function.update l i (l i+1) then 1 else 0) := by
  by_cases h : k = Function.update l i (l i+1)
  · have hi : k i = l i+1 := by rw [h, Function.update_self]
    have hl : l = Function.update k i (k i-1) := by
      funext j
      by_cases hji : j = i
      · subst j; simp only [Function.update_self, hi, Nat.add_sub_cancel]
      · rw [Function.update_of_ne hji, h, Function.update_of_ne hji]
    rw [if_pos h, if_pos hl, mul_one, mul_one, hi]
    push_cast
    rfl
  · by_cases hk : k i = 0
    · simp [h, hk]
    · have hl : l ≠ Function.update k i (k i-1) := by
        intro hl
        apply h
        funext j
        by_cases hji : j = i
        · subst j
          have hli := congrFun hl i
          simp only [Function.update_self] at hli ⊢
          omega
        · rw [Function.update_of_ne hji, hl, Function.update_of_ne hji]
      simp [h, hl]

theorem inner_numberBasis_numberLadder (a : Fin d → ℂ) (l k : Fin d → ℕ) :
    ⟪numberBasis d l, numberLadder a k⟫_ℂ =
      ∑ i, (a i * ((Real.sqrt (k i+1 : ℝ) : ℂ) *
          (if l = Function.update k i (k i+1) then 1 else 0)) -
        starRingEnd ℂ (a i) * ((Real.sqrt (l i+1 : ℝ) : ℂ) *
          (if k = Function.update l i (l i+1) then 1 else 0))) := by
  simp only [numberLadder, inner_sum, inner_sub_right, inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis d).orthonormal, mul_assoc]
  simp_rw [number_lowering_entry]

end Cloning.MultimodeCoherent

namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def wordFockOccupation (w : List (PositiveRoot d)) : Fin (Fintype.card (PositiveRoot d)) → ℕ :=
  fockOccupation d (fun a => w.count a)

def wordNumberVector (w : List (PositiveRoot d)) : RootFock d :=
  numberBasis _ (wordFockOccupation w)

def rootFockAmplitude (z : PositiveRoot d → ℂ) : Fin (Fintype.card (PositiveRoot d)) → ℂ :=
  fun i => z ((Fintype.equivFin (PositiveRoot d)).symm i)

theorem wordFockOccupation_eq_iff (u v : List (PositiveRoot d)) :
    wordFockOccupation u = wordFockOccupation v ↔ u.Perm v := by
  rw [wordFockOccupation, wordFockOccupation]
  constructor
  · intro h
    exact List.perm_iff_count.mpr (congrFun (fockOccupation_injective d h))
  · intro h
    congr 1
    funext a
    exact h.count_eq a

theorem wordFockOccupation_cons (a : PositiveRoot d) (w : List (PositiveRoot d)) :
    wordFockOccupation (a::w) = Function.update (wordFockOccupation w)
      ((Fintype.equivFin (PositiveRoot d)) a) (w.count a+1) := by
  funext i
  by_cases hi : i = (Fintype.equivFin (PositiveRoot d)) a
  · subst i
    simp [wordFockOccupation, fockOccupation, List.count_cons_self]
  · have ha : (Fintype.equivFin (PositiveRoot d)).symm i ≠ a := by
      intro h
      apply hi
      simpa using congrArg (Fintype.equivFin (PositiveRoot d)) h
    simp [wordFockOccupation, fockOccupation, Function.update_of_ne hi,
      List.count_cons, ha, Ne.symm ha]

theorem inner_wordNumberVector_ladder (z : PositiveRoot d → ℂ)
    (u v : List (PositiveRoot d)) :
    ⟪wordNumberVector u, numberLadder (rootFockAmplitude z) (wordFockOccupation v)⟫_ℂ =
      oscillatorEntry z u v := by
  rw [wordNumberVector, inner_numberBasis_numberLadder]
  rw [← Equiv.sum_comp (Fintype.equivFin (PositiveRoot d))]
  unfold oscillatorEntry
  apply Finset.sum_congr rfl
  intro a _
  simp only [rootFockAmplitude, wordFockOccupation, fockOccupation, Equiv.symm_apply_apply]
  have hu : (wordFockOccupation u = Function.update (wordFockOccupation v)
      ((Fintype.equivFin (PositiveRoot d)) a) (v.count a+1)) ↔ u.Perm (a::v) := by
    rw [← wordFockOccupation_cons, wordFockOccupation_eq_iff]
  have hv : (wordFockOccupation v = Function.update (wordFockOccupation u)
      ((Fintype.equivFin (PositiveRoot d)) a) (u.count a+1)) ↔ v.Perm (a::u) := by
    rw [← wordFockOccupation_cons, wordFockOccupation_eq_iff]
  simp only [wordFockOccupation, fockOccupation] at hu hv
  by_cases hpu : u.Perm (a::v) <;> by_cases hpv : v.Perm (a::u) <;>
    simp [creationEntry, annihilationEntry, hu, hv, hpu, hpv, Complex.star_def]

theorem cutoffNumberFrame_eq_word (R : ℕ) (i : CutoffIndex d R) :
    cutoffNumberFrame d R i = wordNumberVector (cutoffWord d R i) := by
  unfold cutoffNumberFrame wordNumberVector wordFockOccupation cutoffWord
  congr 2
  funext a
  exact (canonicalWord_count (cutoffOccupation d R i).val a).symm

theorem oscillatorCutoffMatrix_eq_numberLadder (Q : ℕ) (z : PositiveRoot d → ℂ)
    (i j : CutoffIndex d Q) :
    oscillatorCutoffMatrix Q z i j =
      ⟪cutoffNumberFrame d Q i,
        numberLadder (rootFockAmplitude z) (wordFockOccupation (cutoffWord d Q j))⟫_ℂ := by
  rw [cutoffNumberFrame_eq_word, inner_wordNumberVector_ladder]
  rfl

end Cloning.TensorLocalUnitary
