import Cloning.YoungGeneralTableaux
import Mathlib.Data.Finset.Max

/-!
# Reversible row insertion on literal letter-count arrays

A weakly increasing row is represented by the multiplicity of each letter.
Insertion replaces the least occupied letter strictly above the input;
reverse insertion replaces the greatest occupied letter strictly below the
returned letter. These are the actual RSK row operations, with their local
inverse and monomial-conservation laws proved below.
-/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

abbrev RowContent (d : ℕ) := Fin d → ℕ

def rowAdd {d : ℕ} (A : RowContent d) (x : Fin d) : RowContent d :=
  Function.update A x (A x + 1)

def rowRemove {d : ℕ} (A : RowContent d) (x : Fin d) : RowContent d :=
  Function.update A x (A x - 1)

def rowReplace {d : ℕ} (A : RowContent d) (x y : Fin d) : RowContent d :=
  rowAdd (rowRemove A y) x

def rowBumpCandidates {d : ℕ} (A : RowContent d) (x : Fin d) : Finset (Fin d) :=
  Finset.univ.filter (fun y => x < y ∧ 0 < A y)

def rowReverseCandidates {d : ℕ} (A : RowContent d) (y : Fin d) : Finset (Fin d) :=
  Finset.univ.filter (fun x => x < y ∧ 0 < A x)

def rowBump {d : ℕ} (A : RowContent d) (x : Fin d) : Option (Fin d) :=
  if h : (rowBumpCandidates A x).Nonempty then some ((rowBumpCandidates A x).min' h)
  else none

def rowReverseBump {d : ℕ} (A : RowContent d) (y : Fin d) : Option (Fin d) :=
  if h : (rowReverseCandidates A y).Nonempty then some ((rowReverseCandidates A y).max' h)
  else none

def rowInserted {d : ℕ} (A : RowContent d) (x : Fin d) : RowContent d :=
  match rowBump A x with
  | none => rowAdd A x
  | some y => rowReplace A x y

def rowReversed {d : ℕ} (A : RowContent d) (y : Fin d) : RowContent d :=
  match rowReverseBump A y with
  | none => A
  | some x => rowReplace A y x

theorem rowBump_eq_some_iff {d : ℕ} (A : RowContent d) (x y : Fin d) :
    rowBump A x = some y ↔ x < y ∧ 0 < A y ∧
      ∀ z, x < z → 0 < A z → y ≤ z := by
  classical
  constructor
  · intro he
    unfold rowBump at he
    split_ifs at he with h
    · have hmin := Finset.min'_mem (rowBumpCandidates A x) h
      have hy : (rowBumpCandidates A x).min' h = y := Option.some.inj he
      rw [hy] at hmin
      obtain ⟨_, hxy, hypos⟩ := Finset.mem_filter.mp hmin
      refine ⟨hxy, hypos, fun z hxz hzpos => ?_⟩
      rw [← hy]
      exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz, hzpos⟩)
  · rintro ⟨hxy, hypos, hmin⟩
    have hymem : y ∈ rowBumpCandidates A x := by simp [rowBumpCandidates, hxy, hypos]
    have hs : (rowBumpCandidates A x).Nonempty := ⟨y, hymem⟩
    rw [rowBump, dif_pos hs]
    congr 1
    apply le_antisymm (Finset.min'_le _ _ hymem)
    have hm := Finset.mem_filter.mp (Finset.min'_mem (rowBumpCandidates A x) hs)
    exact hmin _ hm.2.1 hm.2.2

theorem rowReverseBump_eq_some_iff {d : ℕ} (A : RowContent d) (y x : Fin d) :
    rowReverseBump A y = some x ↔ x < y ∧ 0 < A x ∧
      ∀ z, z < y → 0 < A z → z ≤ x := by
  classical
  constructor
  · intro he
    unfold rowReverseBump at he
    split_ifs at he with h
    · have hmax := Finset.max'_mem (rowReverseCandidates A y) h
      have hx : (rowReverseCandidates A y).max' h = x := Option.some.inj he
      rw [hx] at hmax
      obtain ⟨_, hxy, hxpos⟩ := Finset.mem_filter.mp hmax
      refine ⟨hxy, hxpos, fun z hzy hzpos => ?_⟩
      rw [← hx]
      exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy, hzpos⟩)
  · rintro ⟨hxy, hxpos, hmax⟩
    have hxmem : x ∈ rowReverseCandidates A y := by
      simp [rowReverseCandidates, hxy, hxpos]
    have hs : (rowReverseCandidates A y).Nonempty := ⟨x, hxmem⟩
    rw [rowReverseBump, dif_pos hs]
    congr 1
    apply le_antisymm _ (Finset.le_max' _ _ hxmem)
    apply Finset.max'_le
    intro z hz
    obtain ⟨_, hzy, hzpos⟩ := Finset.mem_filter.mp hz
    exact hmax z hzy hzpos

theorem rowBump_eq_none_iff {d : ℕ} (A : RowContent d) (x : Fin d) :
    rowBump A x = none ↔ ∀ y, x < y → A y = 0 := by
  classical
  simp only [rowBump]
  split_ifs with h
  · constructor
    · simp
    · intro he
      obtain ⟨y, hy⟩ := h
      obtain ⟨_, hxy, hypos⟩ := Finset.mem_filter.mp hy
      have := he y hxy
      omega
  · simp only [true_iff]
    intro y hxy
    by_contra hy
    exact h ⟨y, by simp [rowBumpCandidates, hxy, Nat.pos_of_ne_zero hy]⟩

theorem rowReplace_cancel {d : ℕ} (A : RowContent d) (x y : Fin d)
    (hxy : x ≠ y) (hy : 0 < A y) :
    rowReplace (rowReplace A x y) y x = A := by
  classical
  funext z
  by_cases hzx : z = x
  · subst z
    simp [rowReplace, rowAdd, rowRemove, hxy, hxy.symm]
  · by_cases hzy : z = y
    · subst z
      simp only [rowReplace, rowAdd, rowRemove, Function.update_apply, hxy, hxy.symm,
        if_true, if_false]
      omega
    · simp [rowReplace, rowAdd, rowRemove, hzx, hzy, hxy, hxy.symm]

/-- The reverse search recovers exactly the input letter of a forward bump. -/
theorem rowReverseBump_after_insert {d : ℕ} (A : RowContent d) (x y : Fin d)
    (h : rowBump A x = some y) : rowReverseBump (rowInserted A x) y = some x := by
  classical
  obtain ⟨hxy, hypos, hmin⟩ := (rowBump_eq_some_iff A x y).mp h
  rw [rowInserted, h]
  apply (rowReverseBump_eq_some_iff _ _ _).mpr
  refine ⟨hxy, ?_, ?_⟩
  · simp [rowReplace, rowAdd, rowRemove, ne_of_lt hxy]
  · intro z hzy hzpos
    by_contra hzx
    have hxz : x < z := lt_of_not_ge hzx
    have hzold : 0 < A z := by
      simpa [rowReplace, rowAdd, rowRemove, Function.update_apply,
        ne_of_gt hxz, ne_of_lt hzy, ne_of_lt hxy] using hzpos
    exact (not_le_of_gt hzy) (hmin z hxz hzold)

/-- Forward insertion followed by its selected reverse step restores the row. -/
theorem rowReversed_after_insert {d : ℕ} (A : RowContent d) (x y : Fin d)
    (h : rowBump A x = some y) : rowReversed (rowInserted A x) y = A := by
  rw [rowReversed, rowReverseBump_after_insert A x y h, rowInserted, h]
  obtain ⟨hxy, hypos, _⟩ := (rowBump_eq_some_iff A x y).mp h
  exact rowReplace_cancel A x y (ne_of_lt hxy) hypos

/-- Conversely, a reverse bump is recovered by forward insertion. -/
theorem rowBump_after_reverse {d : ℕ} (A : RowContent d) (y x : Fin d)
    (h : rowReverseBump A y = some x) : rowBump (rowReversed A y) x = some y := by
  classical
  obtain ⟨hxy, hxpos, hmax⟩ := (rowReverseBump_eq_some_iff A y x).mp h
  rw [rowReversed, h]
  apply (rowBump_eq_some_iff _ _ _).mpr
  refine ⟨hxy, ?_, ?_⟩
  · simp [rowReplace, rowAdd, rowRemove, (ne_of_lt hxy).symm]
  · intro z hxz hzpos
    by_contra hzy
    have hzy' : z < y := lt_of_not_ge hzy
    have hzold : 0 < A z := by
      simpa [rowReplace, rowAdd, rowRemove, Function.update_apply,
        ne_of_gt hxz, ne_of_lt hzy', (ne_of_lt hxy).symm] using hzpos
    exact (not_le_of_gt hxz) (hmax z hzy' hzold)

theorem rowInserted_after_reverse {d : ℕ} (A : RowContent d) (y x : Fin d)
    (h : rowReverseBump A y = some x) : rowInserted (rowReversed A y) x = A := by
  rw [rowInserted, rowBump_after_reverse A y x h, rowReversed, h]
  obtain ⟨hxy, hxpos, _⟩ := (rowReverseBump_eq_some_iff A y x).mp h
  exact rowReplace_cancel A y x (ne_of_lt hxy).symm hxpos

/-- Literal conservation of each letter multiplicity at a bump. -/
theorem rowReplace_content {d : ℕ} (A : RowContent d) (x y j : Fin d)
    (hxy : x ≠ y) (hy : 0 < A y) :
    rowReplace A x y j + (if j = y then 1 else 0) =
      A j + (if j = x then 1 else 0) := by
  classical
  by_cases hjx : j = x
  · subst j
    simp [rowReplace, rowAdd, rowRemove, hxy]
  · by_cases hjy : j = y
    · subst j
      simp only [rowReplace, rowAdd, rowRemove, Function.update_apply, hxy, hxy.symm,
        if_true, if_false, add_zero]
      omega
    · simp [rowReplace, rowAdd, rowRemove, hjx, hjy, hxy]

theorem rowReplace_mass {d : ℕ} (A : RowContent d) (x y : Fin d)
    (hxy : x ≠ y) (hy : 0 < A y) : ∑ j, rowReplace A x y j = ∑ j, A j := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun j _ => rowReplace_content A x y j hxy hy)
  simp only [Finset.sum_add_distrib] at h
  simpa using h

def rowPrefix {d : ℕ} (A : RowContent d) (k : Fin d) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ≤ k), A j

def rowStrictPrefix {d : ℕ} (A : RowContent d) (k : Fin d) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => j < k), A j

theorem monotone_rowPrefix {d : ℕ} (A : RowContent d) : Monotone (rowPrefix A) := by
  intro b k hbk
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans hbk

theorem monotone_rowStrictPrefix {d : ℕ} (A : RowContent d) :
    Monotone (rowStrictPrefix A) := by
  intro b k hbk
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans_le hbk

theorem rowPrefix_le_strictPrefix {d : ℕ} (A : RowContent d) (b k : Fin d)
    (hbk : b < k) : rowPrefix A b ≤ rowStrictPrefix A k := by
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans_lt hbk

theorem rowPrefix_eq_of_no_entries {d : ℕ} (A : RowContent d) (b k : Fin d)
    (hbk : b ≤ k) (hzero : ∀ j, b < j → j ≤ k → A j = 0) :
    rowPrefix A k = rowPrefix A b := by
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans hbk
  · intro j hj hjnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj hjnot
    exact hzero j hjnot hj

theorem rowStrictPrefix_slack {d : ℕ} (A : RowContent d) (b k : Fin d)
    (hbk : b < k) (hb : 0 < A b) : rowStrictPrefix A b + 1 ≤ rowStrictPrefix A k := by
  have hs : insert b (Finset.univ.filter (fun j => j < b)) ⊆
      Finset.univ.filter (fun j => j < k) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hj with rfl | hj
    · exact hbk
    · exact hj.trans hbk
  have h := Finset.sum_le_sum_of_subset (f := A) hs
  rw [Finset.sum_insert (by simp)] at h
  change A b + rowStrictPrefix A b ≤ rowStrictPrefix A k at h
  omega

theorem rowReplace_sum {d : ℕ} (A : RowContent d) (x y : Fin d)
    (hxy : x ≠ y) (hy : 0 < A y) (s : Finset (Fin d)) :
    (∑ j ∈ s, rowReplace A x y j) + (if y ∈ s then 1 else 0) =
      (∑ j ∈ s, A j) + (if x ∈ s then 1 else 0) := by
  have h := Finset.sum_congr (s₁ := s) rfl
    (fun j _ => rowReplace_content A x y j hxy hy)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq'] using h

/-- Replacing the least larger letter increases exactly the intermediate
weak prefixes. -/
theorem rowReplace_prefix {d : ℕ} (A : RowContent d) (x y k : Fin d)
    (hxy : x < y) (hy : 0 < A y) :
    rowPrefix (rowReplace A x y) k = rowPrefix A k +
      (if x ≤ k ∧ k < y then 1 else 0) := by
  have h := rowReplace_sum A x y (ne_of_lt hxy) hy
    (Finset.univ.filter (fun j => j ≤ k))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  change rowPrefix (rowReplace A x y) k + (if y ≤ k then 1 else 0) =
    rowPrefix A k + (if x ≤ k then 1 else 0) at h
  split_ifs at h ⊢ <;> omega

theorem rowReplace_strictPrefix {d : ℕ} (A : RowContent d) (x y k : Fin d)
    (hxy : x < y) (hy : 0 < A y) :
    rowStrictPrefix (rowReplace A x y) k = rowStrictPrefix A k +
      (if x < k ∧ k ≤ y then 1 else 0) := by
  have h := rowReplace_sum A x y (ne_of_lt hxy) hy
    (Finset.univ.filter (fun j => j < k))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  change rowStrictPrefix (rowReplace A x y) k + (if y < k then 1 else 0) =
    rowStrictPrefix A k + (if x < k then 1 else 0) at h
  split_ifs at h ⊢ <;> omega

theorem rowAdd_content {d : ℕ} (A : RowContent d) (x j : Fin d) :
    rowAdd A x j = A j + (if j = x then 1 else 0) := by
  by_cases h : j = x
  · subst j; simp [rowAdd]
  · simp [rowAdd, h]

theorem rowAdd_prefix {d : ℕ} (A : RowContent d) (x k : Fin d) :
    rowPrefix (rowAdd A x) k = rowPrefix A k + (if x ≤ k then 1 else 0) := by
  simp only [rowPrefix, rowAdd_content, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

theorem rowAdd_strictPrefix {d : ℕ} (A : RowContent d) (x k : Fin d) :
    rowStrictPrefix (rowAdd A x) k = rowStrictPrefix A k + (if x < k then 1 else 0) := by
  simp only [rowStrictPrefix, rowAdd_content, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

theorem rowInserted_prefix_of_bump {d : ℕ} (A : RowContent d) (x y k : Fin d)
    (h : rowBump A x = some y) :
    rowPrefix (rowInserted A x) k = rowPrefix A k +
      (if x ≤ k ∧ k < y then 1 else 0) := by
  rw [rowInserted, h]
  obtain ⟨hxy, hy, _⟩ := (rowBump_eq_some_iff A x y).mp h
  exact rowReplace_prefix A x y k hxy hy

theorem rowInserted_prefix_of_none {d : ℕ} (A : RowContent d) (x k : Fin d)
    (h : rowBump A x = none) :
    rowPrefix (rowInserted A x) k = rowPrefix A k + (if x ≤ k then 1 else 0) := by
  rw [rowInserted, h]
  exact rowAdd_prefix A x k

theorem rowInserted_strictPrefix_of_bump {d : ℕ} (A : RowContent d) (x y k : Fin d)
    (h : rowBump A x = some y) :
    rowStrictPrefix (rowInserted A x) k = rowStrictPrefix A k +
      (if x < k ∧ k ≤ y then 1 else 0) := by
  rw [rowInserted, h]
  obtain ⟨hxy, hy, _⟩ := (rowBump_eq_some_iff A x y).mp h
  exact rowReplace_strictPrefix A x y k hxy hy

theorem rowInserted_strictPrefix_of_none {d : ℕ} (A : RowContent d) (x k : Fin d)
    (h : rowBump A x = none) :
    rowStrictPrefix (rowInserted A x) k = rowStrictPrefix A k + (if x < k then 1 else 0) := by
  rw [rowInserted, h]
  exact rowAdd_strictPrefix A x k

@[simp] theorem rowRemove_rowAdd {d : ℕ} (A : RowContent d) (x : Fin d) :
    rowRemove (rowAdd A x) x = A := by
  funext j
  by_cases h : j = x
  · subst j; simp [rowRemove, rowAdd]
  · simp [rowRemove, rowAdd, h]

theorem rowAdd_rowRemove {d : ℕ} (A : RowContent d) (x : Fin d) (hx : 0 < A x) :
    rowAdd (rowRemove A x) x = A := by
  funext j
  by_cases h : j = x
  · subst j; simp only [rowRemove, rowAdd, Function.update_self]; omega
  · simp [rowRemove, rowAdd, h]

def rowLast {d : ℕ} (A : RowContent d) : Option (Fin d) :=
  if h : (Finset.univ.filter (fun x => 0 < A x)).Nonempty then
    some ((Finset.univ.filter (fun x => 0 < A x)).max' h)
  else none

def rowDeleteLast {d : ℕ} (A : RowContent d) : RowContent d :=
  match rowLast A with
  | none => A
  | some x => rowRemove A x

theorem rowLast_eq_some_iff {d : ℕ} (A : RowContent d) (x : Fin d) :
    rowLast A = some x ↔ 0 < A x ∧ ∀ y, 0 < A y → y ≤ x := by
  classical
  constructor
  · intro he
    unfold rowLast at he
    split_ifs at he with hs
    have he' := Option.some.inj he
    have hm := Finset.max'_mem _ hs
    rw [he'] at hm
    refine ⟨(Finset.mem_filter.mp hm).2, ?_⟩
    intro y hy
    rw [← he']
    exact Finset.le_max' _ _ (by simp [hy])
  · rintro ⟨hx, hmax⟩
    have hm : x ∈ Finset.univ.filter (fun y => 0 < A y) := by simp [hx]
    have hs : (Finset.univ.filter (fun y => 0 < A y)).Nonempty := ⟨x, hm⟩
    rw [rowLast, dif_pos hs]
    congr 1
    apply le_antisymm _ (Finset.le_max' _ _ hm)
    apply Finset.max'_le
    intro y hy
    exact hmax y (Finset.mem_filter.mp hy).2

theorem rowLast_after_terminal_insert {d : ℕ} (A : RowContent d) (x : Fin d)
    (h : rowBump A x = none) : rowLast (rowInserted A x) = some x := by
  rw [rowInserted, h]
  apply (rowLast_eq_some_iff _ _).mpr
  refine ⟨by simp [rowAdd], ?_⟩
  intro y hy
  by_contra hxy
  have hxy' : x < y := lt_of_not_ge hxy
  have hyzero := (rowBump_eq_none_iff A x).mp h y hxy'
  simp [rowAdd, ne_of_gt hxy', hyzero] at hy

theorem rowDeleteLast_after_terminal_insert {d : ℕ} (A : RowContent d) (x : Fin d)
    (h : rowBump A x = none) : rowDeleteLast (rowInserted A x) = A := by
  rw [rowDeleteLast, rowLast_after_terminal_insert A x h, rowInserted, h]
  exact rowRemove_rowAdd A x

theorem rowBump_after_deleteLast {d : ℕ} (A : RowContent d) (x : Fin d)
    (h : rowLast A = some x) : rowBump (rowDeleteLast A) x = none := by
  rw [rowDeleteLast, h]
  apply (rowBump_eq_none_iff _ _).mpr
  intro y hxy
  have hyzero : A y = 0 := by
    have hmax := (rowLast_eq_some_iff A x).mp h
    by_contra hy
    exact (not_le_of_gt hxy) (hmax.2 y (Nat.pos_of_ne_zero hy))
  simp [rowRemove, ne_of_gt hxy, hyzero]

theorem rowInserted_after_deleteLast {d : ℕ} (A : RowContent d) (x : Fin d)
    (h : rowLast A = some x) : rowInserted (rowDeleteLast A) x = A := by
  rw [rowInserted, rowBump_after_deleteLast A x h, rowDeleteLast, h]
  exact rowAdd_rowRemove A x ((rowLast_eq_some_iff A x).mp h).1

theorem rowAdd_mass {d : ℕ} (A : RowContent d) (x : Fin d) :
    (∑ j, rowAdd A x j) = (∑ j, A j) + 1 := by
  simp [rowAdd_content, Finset.sum_add_distrib]

def rowMonomial {d : ℕ} (p : Fin d → ℝ) (A : RowContent d) : ℝ :=
  ∏ j, p j ^ A j

/-- Multiplicative conservation has no division and remains valid at zero
probabilities. -/
theorem rowReplace_monomial {d : ℕ} (p : Fin d → ℝ) (A : RowContent d)
    (x y : Fin d) (hxy : x ≠ y) (hy : 0 < A y) :
    rowMonomial p (rowReplace A x y) * p y = rowMonomial p A * p x := by
  have h := Finset.prod_congr (s₁ := Finset.univ) rfl
    (fun j _ => congrArg (fun n : ℕ => p j ^ n) (rowReplace_content A x y j hxy hy))
  simp only [pow_add, Finset.prod_mul_distrib] at h
  simpa only [rowMonomial, apply_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true] using h

theorem rowAdd_monomial {d : ℕ} (p : Fin d → ℝ) (A : RowContent d) (x : Fin d) :
    rowMonomial p (rowAdd A x) = rowMonomial p A * p x := by
  simp only [rowMonomial, rowAdd_content, pow_add, Finset.prod_mul_distrib]
  simp only [apply_ite, pow_one, pow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true]

end Cloning.YoungGeneral
