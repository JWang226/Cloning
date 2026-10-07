import Cloning.TensorPBWOrder
import Cloning.TensorPBWWeight
import Mathlib.Data.Finsupp.Multiset

/-! Finite occupation indices and canonical ordered positive-root words.
All combinatorics is independent of the tensor representation. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- The weighted height of a positive-root occupation function. -/
def occupationHeight (k : PositiveRoot d → ℕ) : ℕ := ∑ a, a.height * k a

/-- Occupations whose total root height is at most the fixed cutoff. -/
def HeightOccupation (d R : ℕ) := {k : PositiveRoot d → ℕ // occupationHeight k ≤ R}

theorem HeightOccupation.apply_le {R : ℕ} (k : HeightOccupation d R)
    (a : PositiveRoot d) : k.val a ≤ R := by
  have hpos := a.height_pos
  have hsum : a.height * k.val a ≤ occupationHeight k.val := by
    unfold occupationHeight
    exact Finset.single_le_sum (f := fun r : PositiveRoot d => r.height * k.val r)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  exact (Nat.le_mul_of_pos_left _ hpos).trans (hsum.trans k.property)

def HeightOccupation.toBox {R : ℕ} (k : HeightOccupation d R) :
    PositiveRoot d → Fin (R + 1) := fun a => ⟨k.val a, Nat.lt_succ_of_le (k.apply_le a)⟩

theorem HeightOccupation.toBox_injective {R : ℕ} :
    Function.Injective (@HeightOccupation.toBox d R) := by
  intro k l h
  apply Subtype.ext
  funext a
  exact congrArg Fin.val (congrFun h a)

instance {R : ℕ} : Fintype (HeightOccupation d R) :=
  Fintype.ofInjective HeightOccupation.toBox HeightOccupation.toBox_injective

theorem HeightOccupation.card_le (R : ℕ) :
    Fintype.card (HeightOccupation d R) ≤ (R + 1) ^ Fintype.card (PositiveRoot d) := by
  simpa using Fintype.card_le_of_injective
    (@HeightOccupation.toBox d R) HeightOccupation.toBox_injective

/-- The multiset with exactly the prescribed root occupations. -/
def occupationMultiset (k : PositiveRoot d → ℕ) : Multiset (PositiveRoot d) :=
  (Finsupp.equivFunOnFinite.symm k).toMultiset

@[simp] theorem occupationMultiset_count (k : PositiveRoot d → ℕ) (a : PositiveRoot d) :
    (occupationMultiset k).count a = k a := by
  simp [occupationMultiset]

/-- The roots occur in ascending `rootKey` order. In the operator convention
used by `loweringWord`, the leftmost root acts last. -/
def canonicalWord (k : PositiveRoot d → ℕ) : List (PositiveRoot d) :=
  (occupationMultiset k).toList.mergeSort (fun a b => rootKey a ≤ rootKey b)

@[simp] theorem canonicalWord_count (k : PositiveRoot d → ℕ) (a : PositiveRoot d) :
    (canonicalWord k).count a = k a := by
  rw [canonicalWord, (List.mergeSort_perm _ _).count_eq]
  have h := Multiset.coe_count a (occupationMultiset k).toList
  rw [Multiset.coe_toList] at h
  convert h.symm.trans (occupationMultiset_count k a) using 1
  simp only [List.count, beq_eq_decide]

theorem canonicalWord_ordered (k : PositiveRoot d → ℕ) : RootOrdered (canonicalWord k) := by
  have ht : ∀ a b c : PositiveRoot d, decide (rootKey a ≤ rootKey b) = true →
      decide (rootKey b ≤ rootKey c) = true → decide (rootKey a ≤ rootKey c) = true := by
    intro a b c hab hbc
    exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have htotal : ∀ a b : PositiveRoot d,
      (decide (rootKey a ≤ rootKey b) || decide (rootKey b ≤ rootKey a)) = true := by
    intro a b
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (rootKey a) (rootKey b)
  simpa only [RootOrdered, canonicalWord, decide_eq_true_eq] using
    List.pairwise_mergeSort ht htotal (occupationMultiset k).toList

theorem canonicalWord_perm_iff (k l : PositiveRoot d → ℕ) :
    (canonicalWord k).Perm (canonicalWord l) ↔ k = l := by
  constructor
  · intro h
    funext a
    simpa using h.count_eq a
  · rintro rfl
    exact List.Perm.refl _

theorem canonicalWord_injective : Function.Injective (@canonicalWord d) := by
  intro k l h
  exact (canonicalWord_perm_iff k l).mp (h ▸ List.Perm.refl _)

theorem loweringHeight_eq_sum_count (w : List (PositiveRoot d)) :
    loweringHeight w = ∑ a, a.height * w.count a := by
  induction w with
  | nil => simp [loweringHeight]
  | cons r w ih =>
      simp only [loweringHeight, List.count_cons, beq_iff_eq, Nat.mul_add,
        Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte, ih]
      omega

theorem loweringWeight_eq_sum_count (w : List (PositiveRoot d)) (a : Fin d) :
    loweringWeight w a = ∑ r, (w.count r : ℤ) * r.weight a := by
  induction w with
  | nil => simp
  | cons r w ih =>
      simp only [loweringWeight_cons, Pi.add_apply, List.count_cons, beq_iff_eq,
        Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
        Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte, ih]
      omega

theorem list_length_eq_sum_count (w : List (PositiveRoot d)) :
    w.length = ∑ a : PositiveRoot d, w.count a := by
  induction w with
  | nil => simp
  | cons r w ih =>
      simp only [List.length_cons, List.count_cons, beq_iff_eq, Finset.sum_add_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ih]

theorem canonicalWord_counts_perm (w : List (PositiveRoot d)) :
    (canonicalWord (fun a => w.count a)).Perm w := by
  apply List.perm_iff_count.mpr
  intro a
  exact canonicalWord_count _ a

theorem canonicalWord_counts_of_ordered (w : List (PositiveRoot d)) (hw : RootOrdered w) :
    canonicalWord (fun a => w.count a) = w := by
  exact (canonicalWord_counts_perm w).eq_of_pairwise
    (fun a b _ _ hab hba => rootKey_injective (Nat.le_antisymm hab hba))
    (canonicalWord_ordered _) hw

@[simp] theorem canonicalWord_height (k : PositiveRoot d → ℕ) :
    loweringHeight (canonicalWord k) = occupationHeight k := by
  simp [loweringHeight_eq_sum_count, occupationHeight]

theorem canonicalWord_weight (k : PositiveRoot d → ℕ) (a : Fin d) :
    loweringWeight (canonicalWord k) a = ∑ r, (k r : ℤ) * r.weight a := by
  simp [loweringWeight_eq_sum_count]

@[simp] theorem canonicalWord_length (k : PositiveRoot d → ℕ) :
    (canonicalWord k).length = ∑ a, k a := by
  simp [list_length_eq_sum_count]

end Cloning.TensorLie
