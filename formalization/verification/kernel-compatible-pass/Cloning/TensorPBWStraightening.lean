import Cloning.TensorPBWOrder
import Cloning.TensorPBWWeight

/-! Exact physical PBW straightening, preserving both Cartan weight and total
root height. No independence of lowering words is used. -/
noncomputable section
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem rootKey_lt_of_first_lt (a b : PositiveRoot d) (h : a.val.1 < b.val.1) :
    rootKey a < rootKey b := by
  have hb := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
  have ha := a.val.2.isLt
  simp only [Nat.mul_succ] at hb
  simp only [rootKey]
  omega

theorem inverted_roots_not_reverse_composable (a b : PositiveRoot d)
    (h : rootKey b < rootKey a) : b.val.1 ≠ a.val.2 := by
  intro he
  have hab : a.val.1 < b.val.1 := by simpa only [he] using a.property
  exact (Nat.not_lt_of_ge (Nat.le_of_lt h)) (rootKey_lt_of_first_lt a b hab)

/-- At an adjacent inversion in this order, the negative commutator branch is
impossible. The remaining merged root has exactly the sum grading. -/
theorem loweringWord_swap_merge (Ω : TensorRegister n (Fin d))
    (p w : List (PositiveRoot d)) (a b : PositiveRoot d)
    (hinv : rootKey b < rootKey a) (h : a.val.1 = b.val.2) :
    loweringWord Ω (p ++ a :: b :: w) =
      loweringWord Ω (p ++ b :: a :: w) +
      loweringWord Ω (p ++ PositiveRoot.merge a b h :: w) := by
  have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) =>
    T (loweringWord Ω w))
    (collectiveGenerator_commutator (n := n) a.val.2 a.val.1 b.val.2 b.val.1)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    if_pos h, if_neg (inverted_roots_not_reverse_composable a b hinv),
    ContinuousLinearMap.zero_apply, sub_zero] at he
  have he' : loweringWord Ω (a :: b :: w) =
      loweringWord Ω (b :: a :: w) + loweringWord Ω (PositiveRoot.merge a b h :: w) := by
    simpa only [loweringWord, PositiveRoot.merge] using
      (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  simpa only [map_add, loweringOperator_apply, ← loweringWord_append] using
    congrArg (loweringOperator n p) he'

theorem loweringWord_swap_commute (Ω : TensorRegister n (Fin d))
    (p w : List (PositiveRoot d)) (a b : PositiveRoot d)
    (hinv : rootKey b < rootKey a) (h : a.val.1 ≠ b.val.2) :
    loweringWord Ω (p ++ a :: b :: w) = loweringWord Ω (p ++ b :: a :: w) := by
  have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) =>
    T (loweringWord Ω w))
    (collectiveGenerator_commutator (n := n) a.val.2 a.val.1 b.val.2 b.val.1)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    if_neg h, if_neg (inverted_roots_not_reverse_composable a b hinv),
    ContinuousLinearMap.zero_apply, sub_self] at he
  have he' : loweringWord Ω (a :: b :: w) = loweringWord Ω (b :: a :: w) :=
    sub_eq_zero.mp he
  simpa only [loweringOperator_apply, ← loweringWord_append] using
    congrArg (loweringOperator n p) he'

/-- Exact grading and length properties of the bracket term. -/
theorem lowering_merge_grading (p w : List (PositiveRoot d)) (a b : PositiveRoot d)
    (h : a.val.1 = b.val.2) :
    loweringHeight (p ++ PositiveRoot.merge a b h :: w) =
      loweringHeight (p ++ a :: b :: w) ∧
    loweringWeight (p ++ PositiveRoot.merge a b h :: w) =
      loweringWeight (p ++ a :: b :: w) ∧
    (p ++ PositiveRoot.merge a b h :: w).length < (p ++ a :: b :: w).length := by
  constructor
  · simp only [loweringHeight_append, loweringHeight, PositiveRoot.merge_height]
    omega
  constructor
  · simp only [loweringWeight_append, loweringWeight_cons, PositiveRoot.merge_weight]
    abel
  · simp only [List.length_append, List.length_cons]
    omega

/-- Straightening in a fixed submodule. The well-founded measure is the
lexicographic pair (word length, number of inversions). Swaps reduce the second
coordinate; commutator terms reduce the first coordinate. -/
theorem loweringWord_mem_of_ordered
    (Ω : TensorRegister n (Fin d)) (S : Submodule ℂ (TensorRegister n (Fin d)))
    (N H : ℕ) (ν : Fin d → ℤ)
    (hordered : ∀ v, RootOrdered v → v.length ≤ N → loweringHeight v = H →
      loweringWeight v = ν → loweringWord Ω v ∈ S)
    (w : List (PositiveRoot d)) (hlen : w.length ≤ N)
    (hheight : loweringHeight w = H) (hweight : loweringWeight w = ν) :
    loweringWord Ω w ∈ S := by
  have main : ∀ L, ∀ w : List (PositiveRoot d), w.length = L → w.length ≤ N →
      loweringHeight w = H → loweringWeight w = ν → loweringWord Ω w ∈ S := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ihL =>
      have inner : ∀ I, ∀ w : List (PositiveRoot d), w.length = L →
          rootInversions w = I → w.length ≤ N → loweringHeight w = H →
          loweringWeight w = ν → loweringWord Ω w ∈ S := by
        intro I
        induction I using Nat.strong_induction_on with
        | h I ihI =>
          intro w hwL hwI hwN hwH hwν
          by_cases hs : RootOrdered w
          · exact hordered w hs hwN hwH hwν
          obtain ⟨p, a, b, t, rfl, hab⟩ := exists_adjacent_rootInversion w hs
          have hswaplen : (p ++ b :: a :: t).length = L := by simpa using hwL
          have hswapI : rootInversions (p ++ b :: a :: t) < I := by
            have hh := rootInversions_swap p t a b hab
            omega
          have hswapH : loweringHeight (p ++ b :: a :: t) = H := by
            simp only [loweringHeight_append, loweringHeight] at hwH ⊢
            omega
          have hswapν : loweringWeight (p ++ b :: a :: t) = ν := by
            simp only [loweringWeight_append, loweringWeight_cons] at hwν ⊢
            convert hwν using 1 <;> abel
          have hswap := ihI _ hswapI _ hswaplen rfl (by simpa using hwN) hswapH hswapν
          by_cases hc : a.val.1 = b.val.2
          · rw [loweringWord_swap_merge Ω p t a b hab hc]
            apply S.add_mem hswap
            obtain ⟨hmH, hmν, hmlen⟩ := lowering_merge_grading p t a b hc
            exact ihL _ (by omega) _ rfl (by omega) (hmH.trans hwH) (hmν.trans hwν)
          · rw [loweringWord_swap_commute Ω p t a b hab hc]
            exact hswap
      intro w hw hwN hwH hwν
      exact inner (rootInversions w) w hw rfl hwN hwH hwν
  exact main w.length w rfl hlen hheight hweight

/-- The span of ordered words at one exact weight and height, with bounded
length. All grading data are retained by physical straightening. -/
def orderedLoweringSpan (Ω : TensorRegister n (Fin d))
    (N H : ℕ) (ν : Fin d → ℤ) : Submodule ℂ (TensorRegister n (Fin d)) :=
  Submodule.span ℂ {x | ∃ v : List (PositiveRoot d), RootOrdered v ∧ v.length ≤ N ∧
    loweringHeight v = H ∧ loweringWeight v = ν ∧ x = loweringWord Ω v}

theorem loweringWord_mem_orderedLoweringSpan (Ω : TensorRegister n (Fin d))
    (w : List (PositiveRoot d)) :
    loweringWord Ω w ∈ orderedLoweringSpan Ω w.length (loweringHeight w) (loweringWeight w) := by
  apply loweringWord_mem_of_ordered Ω _ _ _ _ _ w le_rfl rfl rfl
  intro v hv hlen hheight hweight
  exact Submodule.subset_span ⟨v, hv, hlen, hheight, hweight, rfl⟩

/-- The actual cutoff is spanned by ordered words within the same exact root
height cutoff. This applies to arbitrary ambient vectors, not only highest ones. -/
theorem cyclicCutoff_eq_ordered_span (Ω : TensorRegister n (Fin d)) (R : ℕ) :
    cyclicCutoff Ω (R : ℤ) = Submodule.span ℂ
      {x | ∃ w : List (PositiveRoot d), RootOrdered w ∧ loweringHeight w ≤ R ∧
        x = loweringWord Ω w} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    apply loweringWord_mem_of_ordered Ω _ w.length (loweringHeight w) (loweringWeight w)
      _ w le_rfl rfl rfl
    intro v hv _ hvH _
    exact Submodule.subset_span ⟨v, hv, by omega, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨w, _, hw, rfl⟩
    exact loweringWord_mem_cyclicCutoff Ω w (by exact_mod_cast hw)

end Cloning.TensorLie
