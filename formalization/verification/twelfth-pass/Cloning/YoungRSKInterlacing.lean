import Cloning.YoungRSKInsertion

/-!
# Column-strict interlacing under actual RSK insertion

For count rows, column strictness says that the number of lower-row letters
at most `k` is no greater than the number of upper-row letters strictly below
`k`.  The proof below verifies this invariant under a genuine bump propagated
from an upper row into the next row.
-/

noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

def RowInterlaces {d : ℕ} (U V : RowContent d) : Prop :=
  ∀ k, rowPrefix V k ≤ rowStrictPrefix U k

theorem rowStrictPrefix_le_prefix {d : ℕ} (A : RowContent d) (k : Fin d) :
    rowStrictPrefix A k ≤ rowPrefix A k := by
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.le

theorem RowInterlaces.trans {d : ℕ} {U V W : RowContent d}
    (hUV : RowInterlaces U V) (hVW : RowInterlaces V W) : RowInterlaces U W := by
  intro k
  exact (hVW k).trans ((rowStrictPrefix_le_prefix V k).trans (hUV k))

theorem rowInserted_strictPrefix_ge {d : ℕ} (A : RowContent d) (x k : Fin d) :
    rowStrictPrefix A k ≤ rowStrictPrefix (rowInserted A x) k := by
  cases h : rowBump A x with
  | none => rw [rowInserted_strictPrefix_of_none A x k h]; omega
  | some y => rw [rowInserted_strictPrefix_of_bump A x y k h]; omega

theorem RowInterlaces.insert_upper {d : ℕ} {U V : RowContent d}
    (hUV : RowInterlaces U V) (x : Fin d) : RowInterlaces (rowInserted U x) V := by
  intro k
  exact (hUV k).trans (rowInserted_strictPrefix_ge U x k)

/-- A bumped letter inserted into the next row preserves strict columns.
Both bumping and terminal append cases are handled by the actual algorithm. -/
theorem RowInterlaces.insert_bumped {d : ℕ} {U V : RowContent d}
    (hUV : RowInterlaces U V) (a b : Fin d) (hb : rowBump U a = some b) :
    RowInterlaces (rowInserted U a) (rowInserted V b) := by
  obtain ⟨hab, hbpos, _⟩ := (rowBump_eq_some_iff U a b).mp hb
  intro k
  rw [rowInserted_strictPrefix_of_bump U a b k hb]
  cases hc : rowBump V b with
  | none =>
    rw [rowInserted_prefix_of_none V b k hc]
    by_cases hbk : b ≤ k
    · rw [if_pos hbk]
      rcases eq_or_lt_of_le hbk with rfl | hbk
      · rw [if_pos ⟨hab, le_rfl⟩]
        exact Nat.add_le_add_right (hUV b) 1
      · have he := rowPrefix_eq_of_no_entries V b k hbk.le
          (fun j hbj _ ↦ (rowBump_eq_none_iff V b).mp hc j hbj)
        rw [he]
        have hs := rowStrictPrefix_slack U b k hbk hbpos
        have hu := hUV b
        omega
    · rw [if_neg hbk]
      have hu := hUV k
      omega
  | some c =>
    rw [rowInserted_prefix_of_bump V b c k hc]
    by_cases hchange : b ≤ k ∧ k < c
    · rw [if_pos hchange]
      rcases eq_or_lt_of_le hchange.1 with rfl | hbk
      · rw [if_pos ⟨hab, le_rfl⟩]
        exact Nat.add_le_add_right (hUV b) 1
      · obtain ⟨_, _, hcmin⟩ := (rowBump_eq_some_iff V b c).mp hc
        have he := rowPrefix_eq_of_no_entries V b k hbk.le (fun j hbj hjk ↦ by
          by_contra hj
          have := hcmin j hbj (Nat.pos_of_ne_zero hj)
          exact (not_le_of_gt hchange.2) (this.trans hjk))
        rw [he]
        have hs := rowStrictPrefix_slack U b k hbk hbpos
        have hu := hUV b
        omega
    · rw [if_neg hchange]
      have hu := hUV k
      omega

theorem rowInterlaces_zero {d : ℕ} (U : RowContent d) : RowInterlaces U 0 := by
  intro k
  simp [rowPrefix]

/-- Terminating below the existing final row is also column-strict. -/
theorem RowInterlaces.insert_new_row {d : ℕ} (U : RowContent d) (a b : Fin d)
    (hb : rowBump U a = some b) : RowInterlaces (rowInserted U a) (rowAdd 0 b) := by
  have h := (rowInterlaces_zero U).insert_bumped a b hb
  have hz : rowBump (0 : RowContent d) b = none :=
    (rowBump_eq_none_iff _ _).mpr (fun _ _ ↦ rfl)
  simpa only [rowInserted, hz] using h

/-- The row relation is exactly the column-order clause already present in
the concrete finite tableau definition. -/
theorem semistandardContent_rowInterlaces {d N : ℕ} {μ : Fin d → ℕ}
    {A : ContentArray d N} (hA : IsSemistandardContent μ A) (i j : Fin d) (hij : i < j) :
    RowInterlaces (fun k ↦ (A i k).val) (fun k ↦ (A j k).val) :=
  fun k ↦ hA.2.2 i j k hij

end Cloning.YoungGeneral
