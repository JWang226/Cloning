import Cloning.YoungRSKInsertion

/-!
# Reverse row insertion preserves adjacent column inequalities

An occupied letter in a lower row guarantees an available smaller letter
in the row above. The selected reverse operations preserve the literal
strict-column prefix inequalities, both at a terminal deletion and along
the reverse bumping path.
-/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

theorem rowReverseBump_exists_of_prefix {d : ℕ} (U V : RowContent d) (b : Fin d)
    (hUV : ∀ k, rowPrefix V k ≤ rowStrictPrefix U k) (hb : 0 < V b) :
    ∃ a, rowReverseBump U b = some a := by
  have hb' : V b ≤ rowPrefix V b := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (show b ∈ Finset.univ.filter (fun j => j ≤ b) by simp)
  have hp : 0 < rowStrictPrefix U b := hb.trans_le (hb'.trans (hUV b))
  obtain ⟨a, ha, hUa⟩ := Finset.sum_pos_iff.mp hp
  have hs : (rowReverseCandidates U b).Nonempty := by
    refine ⟨a, ?_⟩
    simpa only [rowReverseCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      using And.intro ((Finset.mem_filter.mp ha).2) hUa
  exact ⟨_, by rw [rowReverseBump, dif_pos hs]⟩

theorem rowReversed_prefix {d : ℕ} (A : RowContent d) (y x k : Fin d)
    (h : rowReverseBump A y = some x) :
    rowPrefix (rowReversed A y) k + (if x ≤ k ∧ k < y then 1 else 0) =
      rowPrefix A k := by
  obtain ⟨hxy, hx, _⟩ := (rowReverseBump_eq_some_iff A y x).mp h
  simp only [rowReversed, h]
  have he := rowReplace_sum A y x (ne_of_lt hxy).symm hx
    (Finset.univ.filter (fun j => j ≤ k))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  change rowPrefix (rowReplace A y x) k + (if x ≤ k then 1 else 0) =
    rowPrefix A k + (if y ≤ k then 1 else 0) at he
  split_ifs at he ⊢ <;> omega

theorem rowReversed_strictPrefix {d : ℕ} (A : RowContent d) (y x k : Fin d)
    (h : rowReverseBump A y = some x) :
    rowStrictPrefix (rowReversed A y) k + (if x < k ∧ k ≤ y then 1 else 0) =
      rowStrictPrefix A k := by
  obtain ⟨hxy, hx, _⟩ := (rowReverseBump_eq_some_iff A y x).mp h
  simp only [rowReversed, h]
  have he := rowReplace_sum A y x (ne_of_lt hxy).symm hx
    (Finset.univ.filter (fun j => j < k))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  change rowStrictPrefix (rowReplace A y x) k + (if x < k then 1 else 0) =
    rowStrictPrefix A k + (if y < k then 1 else 0) at he
  split_ifs at he ⊢ <;> omega

theorem rowRemove_content {d : ℕ} (A : RowContent d) (x j : Fin d) (hx : 0 < A x) :
    rowRemove A x j + (if j = x then 1 else 0) = A j := by
  by_cases hj : j = x
  · subst j
    simp only [rowRemove, Function.update_self, if_true]
    omega
  · simp [rowRemove, hj]

theorem rowRemove_prefix {d : ℕ} (A : RowContent d) (x k : Fin d) (hx : 0 < A x) :
    rowPrefix (rowRemove A x) k + (if x ≤ k then 1 else 0) = rowPrefix A k := by
  have he := Finset.sum_congr
    (s₁ := Finset.univ.filter (fun j => j ≤ k)) rfl
    (fun j _ => rowRemove_content A x j hx)
  simpa only [rowPrefix, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and] using he

theorem rowPrefix_slack {d : ℕ} (A : RowContent d) (k b : Fin d)
    (hkb : k < b) (hb : 0 < A b) : rowPrefix A k + 1 ≤ rowPrefix A b := by
  have hs : insert b (Finset.univ.filter (fun j => j ≤ k)) ⊆
      Finset.univ.filter (fun j => j ≤ b) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hj with rfl | hj
    · exact le_rfl
    · exact hj.trans hkb.le
  have he := Finset.sum_le_sum_of_subset (f := A) hs
  rw [Finset.sum_insert (by simp [not_le_of_gt hkb])] at he
  change A b + rowPrefix A k ≤ rowPrefix A b at he
  omega

theorem rowStrictPrefix_eq_of_no_entries {d : ℕ} (A : RowContent d) (k b : Fin d)
    (hkb : k ≤ b) (hzero : ∀ j, k ≤ j → j < b → A j = 0) :
    rowStrictPrefix A b = rowStrictPrefix A k := by
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans_le hkb
  · intro j hj hjnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj hjnot
    exact hzero j hjnot hj

theorem rowStrictPrefix_eq_at_reverse {d : ℕ} (U : RowContent d) (b a k : Fin d)
    (h : rowReverseBump U b = some a) (hak : a < k) (hkb : k ≤ b) :
    rowStrictPrefix U b = rowStrictPrefix U k := by
  apply rowStrictPrefix_eq_of_no_entries U k b hkb
  intro j hkj hjb
  have hmax := ((rowReverseBump_eq_some_iff U b a).mp h).2.2
  by_contra hj
  exact (not_le_of_gt (hak.trans_le hkj)) (hmax j hjb (Nat.pos_of_ne_zero hj))

/-- A reverse step in the upper row preserves interlacing with any lower
row whose prefixes decrease and whose prefix at the returned letter drops. -/
theorem rowReversed_interlaces_of_prefix {d : ℕ}
    (U V W : RowContent d) (b a : Fin d)
    (hUV : ∀ k, rowPrefix V k ≤ rowStrictPrefix U k)
    (hb : 0 < V b) (hrev : rowReverseBump U b = some a)
    (hWV : ∀ k, rowPrefix W k ≤ rowPrefix V k)
    (hdrop : rowPrefix W b + 1 ≤ rowPrefix V b) :
    ∀ k, rowPrefix W k ≤ rowStrictPrefix (rowReversed U b) k := by
  intro k
  have he := rowReversed_strictPrefix U b a k hrev
  by_cases hk : a < k ∧ k ≤ b
  · rw [if_pos hk] at he
    have hflat := rowStrictPrefix_eq_at_reverse U b a k hrev hk.1 hk.2
    have hslack : rowPrefix W k + 1 ≤ rowPrefix V b := by
      rcases lt_or_eq_of_le hk.2 with hkb | rfl
      · exact (Nat.add_le_add_right (hWV k) 1).trans (rowPrefix_slack V k b hkb hb)
      · exact hdrop
    have hupper := hUV b
    omega
  · rw [if_neg hk, add_zero] at he
    rw [he]
    exact (hWV k).trans (hUV k)

theorem rowReversed_interlaces_remove {d : ℕ} (U V : RowContent d) (b a : Fin d)
    (hUV : ∀ k, rowPrefix V k ≤ rowStrictPrefix U k)
    (hb : 0 < V b) (hrev : rowReverseBump U b = some a) :
    ∀ k, rowPrefix (rowRemove V b) k ≤ rowStrictPrefix (rowReversed U b) k := by
  apply rowReversed_interlaces_of_prefix U V (rowRemove V b) b a hUV hb hrev
  · intro k
    have he := rowRemove_prefix V b k hb
    omega
  · have he := rowRemove_prefix V b b hb
    simpa only [le_refl, if_true] using he.le

theorem rowReversed_interlaces_reverse {d : ℕ} (U V : RowContent d) (c b a : Fin d)
    (hUV : ∀ k, rowPrefix V k ≤ rowStrictPrefix U k)
    (hV : rowReverseBump V c = some b) (hU : rowReverseBump U b = some a) :
    ∀ k, rowPrefix (rowReversed V c) k ≤ rowStrictPrefix (rowReversed U b) k := by
  obtain ⟨hbc, hb, _⟩ := (rowReverseBump_eq_some_iff V c b).mp hV
  apply rowReversed_interlaces_of_prefix U V (rowReversed V c) b a hUV hb hU
  · intro k
    have he := rowReversed_prefix V c b k hV
    omega
  · have he := rowReversed_prefix V c b b hV
    simpa only [le_refl, hbc, and_self, if_true] using he.le

end Cloning.YoungGeneral
