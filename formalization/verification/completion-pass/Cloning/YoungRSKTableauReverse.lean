import Cloning.YoungRSKReverse
import Cloning.YoungRSKTableau

/-! Recursive reverse deletion on a supplied corner, retaining the fixed
number of count rows used by the finite content-array model. -/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

def tableauReverse {d : ℕ} : List (RowContent d) → ℕ → Option (List (RowContent d) × Fin d)
  | [], _ => none
  | U :: T, 0 =>
      match rowLast U with
      | none => none
      | some x => some (rowDeleteLast U :: T, x)
  | U :: T, r + 1 =>
      match tableauReverse T r with
      | none => none
      | some (S, y) =>
          match rowReverseBump U y with
          | none => none
          | some x => some (rowReversed U y :: S, x)

def tableauRemovable {d : ℕ} : List (RowContent d) → ℕ → Prop
  | [], _ => False
  | U :: T, 0 => 0 < ∑ j, U j ∧ ∀ V ∈ T.head?, (∑ j, V j) < ∑ j, U j
  | _ :: T, r + 1 => tableauRemovable T r

theorem tableauReverse_length {d : ℕ} (T S : List (RowContent d)) (r : ℕ) (x : Fin d)
    (h : tableauReverse T r = some (S, x)) : S.length = T.length := by
  induction T generalizing S r x with
  | nil => simp [tableauReverse] at h
  | cons U T ih =>
    cases r with
    | zero =>
      cases hb : rowLast U with
      | none => simp [tableauReverse, hb] at h
      | some b =>
        simp only [tableauReverse, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    | succ r =>
      cases ht : tableauReverse T r with
      | none => simp [tableauReverse, ht] at h
      | some P =>
        obtain ⟨R, b⟩ := P
        cases hb : rowReverseBump U b with
        | none => simp [tableauReverse, ht, hb] at h
        | some a =>
          simp only [tableauReverse, ht, hb, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simpa only [List.length_cons] using congrArg Nat.succ (ih R r b ht)

theorem tableauReverse_corner_lt {d : ℕ} (T S : List (RowContent d)) (r : ℕ) (x : Fin d)
    (h : tableauReverse T r = some (S, x)) : r < T.length := by
  induction T generalizing S r x with
  | nil => simp [tableauReverse] at h
  | cons U T ih =>
    cases r with
    | zero => simp
    | succ r =>
      cases ht : tableauReverse T r with
      | none => simp [tableauReverse, ht] at h
      | some P =>
        obtain ⟨R, b⟩ := P
        exact Nat.succ_lt_succ (ih R r b ht)

/-- A successful reverse path decreases every prefix of its top row and
removes one occurrence at the recovered letter. -/
theorem tableauReverse_head_prefix {d : ℕ} (U : RowContent d)
    (T S : List (RowContent d)) (r : ℕ) (x : Fin d)
    (h : tableauReverse (U :: T) r = some (S, x)) :
    ∃ W R, S = W :: R ∧ 0 < U x ∧
      (∀ k, rowPrefix W k ≤ rowPrefix U k) ∧
      rowPrefix W x + 1 = rowPrefix U x := by
  cases r with
  | zero =>
    cases hb : rowLast U with
    | none => simp [tableauReverse, hb] at h
    | some b =>
      simp only [tableauReverse, hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hbpos := ((rowLast_eq_some_iff U b).mp hb).1
      refine ⟨rowDeleteLast U, T, rfl, hbpos, ?_, ?_⟩
      · intro k
        have he := rowRemove_prefix U b k hbpos
        simp only [rowDeleteLast, hb]
        omega
      · simpa only [rowDeleteLast, hb, le_refl, if_true] using rowRemove_prefix U b b hbpos
  | succ r =>
    cases ht : tableauReverse T r with
    | none => simp [tableauReverse, ht] at h
    | some P =>
      obtain ⟨R, b⟩ := P
      cases hb : rowReverseBump U b with
      | none => simp [tableauReverse, ht, hb] at h
      | some a =>
        simp only [tableauReverse, ht, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hab, hapos, _⟩ := (rowReverseBump_eq_some_iff U b a).mp hb
        refine ⟨rowReversed U b, R, rfl, hapos, ?_, ?_⟩
        · intro k
          have he := rowReversed_prefix U b a k hb
          omega
        · simpa only [le_refl, hab, and_self, if_true] using rowReversed_prefix U b a a hb

theorem rowInterlaces_mass_le {d : ℕ} (U V : RowContent d)
    (hUV : ∀ k, rowPrefix V k ≤ rowStrictPrefix U k) :
    (∑ j, V j) ≤ ∑ j, U j := by
  cases d with
  | zero => simp
  | succ d =>
    have h := hUV (Fin.last d)
    have hv : rowPrefix V (Fin.last d) = ∑ j, V j := by
      simp [rowPrefix, Fin.le_last]
    rw [hv] at h
    exact h.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

theorem rowLast_exists_of_mass {d : ℕ} (U : RowContent d) (hU : 0 < ∑ j, U j) :
    ∃ x, rowLast U = some x := by
  obtain ⟨x, _, hx⟩ := Finset.sum_pos_iff.mp hU
  have hs : (Finset.univ.filter (fun y => 0 < U y)).Nonempty := ⟨x, by simp [hx]⟩
  exact ⟨_, by rw [rowLast, dif_pos hs]⟩

theorem rowRemove_strictPrefix {d : ℕ} (A : RowContent d) (x k : Fin d) (hx : 0 < A x) :
    rowStrictPrefix (rowRemove A x) k + (if x < k then 1 else 0) =
      rowStrictPrefix A k := by
  have he := Finset.sum_congr (s₁ := Finset.univ.filter (fun j => j < k)) rfl
    (fun j _ => rowRemove_content A x j hx)
  simpa only [rowStrictPrefix, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and] using he

theorem rowStrictPrefix_eq_mass_of_last {d : ℕ} (U : RowContent d) (b k : Fin d)
    (hb : rowLast U = some b) (hbk : b < k) : rowStrictPrefix U k = ∑ j, U j := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
  by_contra hjzero
  have hmax := ((rowLast_eq_some_iff U b).mp hb).2 j (Nat.pos_of_ne_zero hjzero)
  exact (not_le_of_gt hbk) (hj.trans hmax)

/-- Removing the final entry at an outer corner preserves its inequalities
with every shorter lower row. -/
theorem rowRemoveLast_interlaces {d : ℕ} (U V : RowContent d) (b : Fin d)
    (hUV : ∀ k, rowPrefix V k ≤ rowStrictPrefix U k)
    (hmass : (∑ j, V j) < ∑ j, U j) (hb : rowLast U = some b) :
    ∀ k, rowPrefix V k ≤ rowStrictPrefix (rowDeleteLast U) k := by
  have hbpos := ((rowLast_eq_some_iff U b).mp hb).1
  intro k
  simp only [rowDeleteLast, hb]
  have he := rowRemove_strictPrefix U b k hbpos
  by_cases hbk : b < k
  · rw [if_pos hbk, rowStrictPrefix_eq_mass_of_last U b k hb hbk] at he
    have hbound : rowPrefix V k ≤ ∑ j, V j :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  · rw [if_neg hbk, add_zero] at he
    rw [he]
    exact hUV k

/-- Reversing the recorded corner exactly recovers insertion's input whenever
insertion stays within the supplied fixed list of rows. -/
theorem tableauReverse_after_insert {d : ℕ} (T : List (RowContent d)) (x : Fin d)
    (hcorner : (tableauInsert T x).2 < T.length) :
    tableauReverse (tableauInsert T x).1 (tableauInsert T x).2 = some (T, x) := by
  induction T generalizing x with
  | nil => simp [tableauInsert] at hcorner
  | cons U T ih =>
    cases hb : rowBump U x with
    | none =>
      simp only [tableauInsert, hb, tableauReverse,
        rowLast_after_terminal_insert U x hb, rowDeleteLast_after_terminal_insert U x hb]
    | some y =>
      have ht : (tableauInsert T y).2 < T.length := by
        simpa only [tableauInsert, hb, List.length_cons, Nat.add_lt_add_iff_right] using hcorner
      simp only [tableauInsert, hb, tableauReverse, ih y ht,
        rowReverseBump_after_insert U x y hb, rowReversed_after_insert U x y hb]

theorem tableauReverse_after_insert_fixed {d : ℕ} (T : List (RowContent d)) (x : Fin d)
    (hT : T.length = d) :
    tableauReverse (tableauInsert T x).1 (tableauInsert T x).2 = some (T, x) := by
  apply tableauReverse_after_insert
  have h := tableauInsert_corner_lt T x
  rw [tableauInsert_fixed_length T x hT] at h
  omega

/-- Every successful reverse deletion is recovered by actual insertion. -/
theorem tableauInsert_after_reverse {d : ℕ} (T S : List (RowContent d)) (r : ℕ) (x : Fin d)
    (h : tableauReverse T r = some (S, x)) : tableauInsert S x = (T, r) := by
  induction T generalizing S r x with
  | nil => simp [tableauReverse] at h
  | cons U T ih =>
    cases r with
    | zero =>
      cases hb : rowLast U with
      | none => simp [tableauReverse, hb] at h
      | some b =>
        simp only [tableauReverse, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [tableauInsert, rowBump_after_deleteLast U b hb,
          rowInserted_after_deleteLast U b hb]
    | succ r =>
      cases ht : tableauReverse T r with
      | none => simp [tableauReverse, ht] at h
      | some P =>
        obtain ⟨R, b⟩ := P
        cases hb : rowReverseBump U b with
        | none => simp [tableauReverse, ht, hb] at h
        | some a =>
          simp only [tableauReverse, ht, hb, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [tableauInsert, rowBump_after_reverse U b a hb,
            rowInserted_after_reverse U b a hb, ih R r b ht]

/-- A genuine removable corner admits reverse deletion, and all strict
column inequalities are preserved throughout the reverse path. -/
theorem tableauReverse_exists_pairwise {d : ℕ} (T : List (RowContent d))
    (hT : List.Pairwise RowInterlaces T) (r : ℕ) (hr : tableauRemovable T r) :
    ∃ S x, tableauReverse T r = some (S, x) ∧ List.Pairwise RowInterlaces S := by
  induction T generalizing r with
  | nil => simp [tableauRemovable] at hr
  | cons U T ih =>
    obtain ⟨hU, hT⟩ := List.pairwise_cons.mp hT
    cases r with
    | zero =>
      obtain ⟨hUpos, hnext⟩ := hr
      obtain ⟨b, hb⟩ := rowLast_exists_of_mass U hUpos
      refine ⟨rowDeleteLast U :: T, b, by simp [tableauReverse, hb], ?_⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_, hT⟩
      intro V hV
      have hmass : (∑ j, V j) < ∑ j, U j := by
        cases T with
        | nil => simp at hV
        | cons W R =>
          have hWU := hnext W (by simp)
          rcases List.mem_cons.mp hV with rfl | hVR
          · exact hWU
          · exact (rowInterlaces_mass_le W V ((List.pairwise_cons.mp hT).1 V hVR)).trans_lt hWU
      exact rowRemoveLast_interlaces U V b (hU V hV) hmass hb
    | succ r =>
      cases T with
      | nil => simp [tableauRemovable] at hr
      | cons V R =>
        obtain ⟨S, b, hS, hSpair⟩ := ih hT r hr
        obtain ⟨W, R', heq, hbpos, hprefix, hdrop⟩ :=
          tableauReverse_head_prefix V R S r b hS
        obtain ⟨a, ha⟩ := rowReverseBump_exists_of_prefix U V b
          (hU V List.mem_cons_self) hbpos
        refine ⟨rowReversed U b :: S, a, by simp [tableauReverse, hS, ha], ?_⟩
        rw [heq] at hSpair ⊢
        apply pairwise_interlaces_cons _ hSpair
        exact rowReversed_interlaces_of_prefix U V W b a
          (hU V List.mem_cons_self) hbpos ha hprefix hdrop.le

theorem tableauReverse_pairwise {d : ℕ} (T S : List (RowContent d))
    (hT : List.Pairwise RowInterlaces T) (r : ℕ) (hr : tableauRemovable T r) (x : Fin d)
    (h : tableauReverse T r = some (S, x)) : List.Pairwise RowInterlaces S := by
  obtain ⟨S', x', h', hp⟩ := tableauReverse_exists_pairwise T hT r hr
  have he := Option.some.inj (h.symm.trans h')
  have heS := congrArg Prod.fst he
  change S = S' at heS
  rwa [heS]

theorem tableauReverse_shape {d : ℕ} (T S : List (RowContent d)) (r : ℕ) (x : Fin d)
    (h : tableauReverse T r = some (S, x)) :
    shapeAdd (tableauShape S) r = tableauShape T := by
  have he := tableauInsert_shape S x
  rw [tableauInsert_after_reverse T S r x h] at he
  exact he.symm

theorem tableauReverse_content {d : ℕ} (T S : List (RowContent d)) (r : ℕ) (x j : Fin d)
    (h : tableauReverse T r = some (S, x)) :
    tableauContent T j = tableauContent S j + (if j = x then 1 else 0) := by
  have he := tableauInsert_content S x j
  rw [tableauInsert_after_reverse T S r x h] at he
  exact he

end Cloning.YoungGeneral
