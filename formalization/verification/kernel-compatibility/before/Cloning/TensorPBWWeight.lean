import Cloning.TensorCyclicFiltration

/-! Exact Cartan weights of actual lowering words. The grading uses the
literal matrix-unit commutator and does not require independence of words. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

/-- The Cartan-weight change caused by the lowering matrix unit `E_{ji}`. -/
def PositiveRoot.weight (r : PositiveRoot d) (a : Fin d) : ℤ :=
  (if a = r.val.2 then 1 else 0) - (if a = r.val.1 then 1 else 0)

/-- The exact additive weight change of a lowering word. -/
def loweringWeight : List (PositiveRoot d) → (Fin d → ℤ)
  | [] => 0
  | r :: w => r.weight + loweringWeight w

@[simp] theorem loweringWeight_nil : loweringWeight ([] : List (PositiveRoot d)) = 0 := rfl

@[simp] theorem loweringWeight_cons (r : PositiveRoot d) (w : List (PositiveRoot d)) :
    loweringWeight (r :: w) = r.weight + loweringWeight w := rfl

@[simp] theorem loweringWeight_append (u v : List (PositiveRoot d)) :
    loweringWeight (u ++ v) = loweringWeight u + loweringWeight v := by
  induction u with
  | nil => simp
  | cons r u ih => simp [ih, add_assoc]

theorem loweringWeight_eq_sum (w : List (PositiveRoot d)) :
    loweringWeight w = (w.map PositiveRoot.weight).sum := by
  induction w with
  | nil => rfl
  | cons r w ih => simp [ih]

theorem loweringWeight_perm {u v : List (PositiveRoot d)} (h : u.Perm v) :
    loweringWeight u = loweringWeight v := by
  rw [loweringWeight_eq_sum, loweringWeight_eq_sum]
  exact (h.map PositiveRoot.weight).sum_eq

/-- Merging two composable positive roots preserves their total Cartan weight. -/
theorem PositiveRoot.weight_merge (i j k : Fin d) (hij : i < j) (hjk : j < k) :
    PositiveRoot.weight (⟨(i, k), lt_trans hij hjk⟩ : PositiveRoot d) =
      PositiveRoot.weight (⟨(i, j), hij⟩ : PositiveRoot d) +
      PositiveRoot.weight (⟨(j, k), hjk⟩ : PositiveRoot d) := by
  funext a
  simp only [PositiveRoot.weight, Pi.add_apply]
  omega

/-- The positive root produced by the nonzero positive term of a lowering
commutator. The arguments occur in operator order. -/
def PositiveRoot.merge (a b : PositiveRoot d) (h : a.val.1 = b.val.2) :
    PositiveRoot d :=
  ⟨(b.val.1, a.val.2), lt_trans (by rw [h]; exact b.property) a.property⟩

@[simp] theorem PositiveRoot.merge_fst (a b : PositiveRoot d) (h : a.val.1 = b.val.2) :
    (a.merge b h).val.1 = b.val.1 := rfl

@[simp] theorem PositiveRoot.merge_snd (a b : PositiveRoot d) (h : a.val.1 = b.val.2) :
    (a.merge b h).val.2 = a.val.2 := rfl

theorem PositiveRoot.merge_weight (a b : PositiveRoot d) (h : a.val.1 = b.val.2) :
    (a.merge b h).weight = a.weight + b.weight := by
  funext k
  simp only [PositiveRoot.weight, merge_fst, merge_snd, Pi.add_apply, h]
  omega

theorem PositiveRoot.merge_height (a b : PositiveRoot d) (h : a.val.1 = b.val.2) :
    (a.merge b h).height = a.height + b.height := by
  have ha := a.property
  have hb := b.property
  have hv := congrArg Fin.val h
  simp only [PositiveRoot.height, merge_fst, merge_snd]
  omega

theorem PositiveRoot.sum_mul_weight (r : PositiveRoot d) (f : Fin d → ℤ) :
    ∑ a, f a * r.weight a = f r.val.2 - f r.val.1 := by
  simp [PositiveRoot.weight, mul_sub, Finset.sum_sub_distrib, mul_ite]

@[simp] theorem PositiveRoot.sum_weight (r : PositiveRoot d) :
    ∑ a, r.weight a = 0 := by
  simpa using r.sum_mul_weight (fun _ => 1)

theorem PositiveRoot.sum_index_mul_weight (r : PositiveRoot d) :
    ∑ a, (a.val : ℤ) * r.weight a = (r.height : ℤ) := by
  rw [r.sum_mul_weight]
  simp only [PositiveRoot.height, Int.natCast_sub (Nat.le_of_lt r.property)]

@[simp] theorem loweringWeight_sum (w : List (PositiveRoot d)) :
    ∑ a, loweringWeight w a = 0 := by
  induction w with
  | nil => simp
  | cons r w ih => simp [Finset.sum_add_distrib, ih]

/-- The total root height is exactly the index-weighted Cartan shift. -/
theorem loweringWeight_index_sum (w : List (PositiveRoot d)) :
    ∑ a, (a.val : ℤ) * loweringWeight w a = (loweringHeight w : ℤ) := by
  induction w with
  | nil => simp [loweringHeight]
  | cons r w ih =>
      simp [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        PositiveRoot.sum_index_mul_weight, ih, loweringHeight]

/-- The exact Cartan/lowering commutator as an identity of actual operators. -/
theorem cartan_lowering_commutator (a : Fin d) (r : PositiveRoot d) :
    collectiveGenerator n a a * collectiveGenerator n r.val.2 r.val.1 -
      collectiveGenerator n r.val.2 r.val.1 * collectiveGenerator n a a =
        (r.weight a : ℂ) • collectiveGenerator n r.val.2 r.val.1 := by
  rw [collectiveGenerator_commutator]
  by_cases haj : a = r.val.2
  · subst a
    have hji : r.val.2 ≠ r.val.1 := ne_of_gt r.property
    simp [PositiveRoot.weight, hji, Ne.symm hji]
  · by_cases hai : a = r.val.1
    · subst a
      simp [PositiveRoot.weight, haj]
    · simp [PositiveRoot.weight, haj, hai, Ne.symm hai]

theorem cartan_lowering_apply (a : Fin d) (r : PositiveRoot d)
    (x : TensorRegister n (Fin d)) :
    collectiveGenerator n a a (collectiveGenerator n r.val.2 r.val.1 x) =
      collectiveGenerator n r.val.2 r.val.1 (collectiveGenerator n a a x) +
        (r.weight a : ℂ) • collectiveGenerator n r.val.2 r.val.1 x := by
  have he := congrArg
    (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T x)
    (cartan_lowering_commutator (n := n) a r)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- Each actual lowering word is a simultaneous Cartan eigenvector with its
exact additive weight. No raising, normalization, or nonvanishing premise is needed. -/
theorem cartan_loweringWord
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (w : List (PositiveRoot d)) (a : Fin d) :
    collectiveGenerator n a a (loweringWord Ω w) =
      (mu a + (loweringWeight w a : ℂ)) • loweringWord Ω w := by
  induction w with
  | nil => simpa [loweringWord] using hweight a
  | cons r w ih =>
      rw [loweringWord, cartan_lowering_apply, ih, map_smul]
      rw [← add_smul]
      congr 1
      simp only [loweringWeight_cons, Pi.add_apply, Int.cast_add]
      ring

end Cloning.TensorLie
