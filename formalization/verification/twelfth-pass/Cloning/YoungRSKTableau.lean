import Cloning.YoungRSKInterlacing

/-!
# Actual RSK insertion through all rows

The recursive algorithm records the row receiving the final new box. Rows
are retained, including zero trailing rows. An alphabet-size bound prevents
insertion from creating a row beyond a fixed list of `d` rows.
-/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

def tableauInsert {d : ℕ} : List (RowContent d) → Fin d → List (RowContent d) × ℕ
  | [], x => ([rowAdd 0 x], 0)
  | U :: T, x =>
    match rowBump U x with
    | none => (rowInserted U x :: T, 0)
    | some y =>
      let out := tableauInsert T y
      (rowInserted U x :: out.1, out.2 + 1)

def tableauContent {d : ℕ} (T : List (RowContent d)) (j : Fin d) : ℕ :=
  (T.map (fun A => A j)).sum

def rowMass {d : ℕ} (A : RowContent d) : ℕ := ∑ j, A j

def tableauShape {d : ℕ} (T : List (RowContent d)) : List ℕ := T.map rowMass

def shapeAdd : List ℕ → ℕ → List ℕ
  | [], _ => [1]
  | m :: M, 0 => (m + 1) :: M
  | m :: M, r + 1 => m :: shapeAdd M r

@[simp] theorem tableauContent_nil {d : ℕ} (j : Fin d) :
    tableauContent ([] : List (RowContent d)) j = 0 := rfl

@[simp] theorem tableauContent_cons {d : ℕ} (U : RowContent d)
    (T : List (RowContent d)) (j : Fin d) :
    tableauContent (U :: T) j = U j + tableauContent T j := rfl

theorem tableauInsert_cons_head {d : ℕ} (U : RowContent d)
    (T : List (RowContent d)) (x : Fin d) :
    ∃ R, (tableauInsert (U :: T) x).1 = rowInserted U x :: R := by
  cases h : rowBump U x <;> simp [tableauInsert, h]

theorem tableauInsert_nonempty {d : ℕ} (T : List (RowContent d)) (x : Fin d) :
    (tableauInsert T x).1 ≠ [] := by
  cases T with
  | nil => simp [tableauInsert]
  | cons U T => obtain ⟨R, hR⟩ := tableauInsert_cons_head U T x; simp [hR]

theorem tableauInsert_corner_lt {d : ℕ} (T : List (RowContent d)) (x : Fin d) :
    (tableauInsert T x).2 < (tableauInsert T x).1.length := by
  induction T generalizing x with
  | nil => simp [tableauInsert]
  | cons U T ih =>
    cases h : rowBump U x with
    | none => simp [tableauInsert, h]
    | some y => simpa [tableauInsert, h] using ih y

theorem tableauInsert_length_of_bound {d : ℕ} (T : List (RowContent d)) (x : Fin d)
    (h : d ≤ x.val + T.length) : (tableauInsert T x).1.length = T.length := by
  induction T generalizing x with
  | nil => have := x.isLt; simp only [List.length_nil, Nat.add_zero] at h; omega
  | cons U T ih =>
    cases hb : rowBump U x with
    | none => simp [tableauInsert, hb]
    | some y =>
      have hxy := ((rowBump_eq_some_iff U x y).mp hb).1
      have hy : d ≤ y.val + T.length := by
        simp only [List.length_cons] at h
        have : x.val < y.val := hxy
        omega
      simp [tableauInsert, hb, ih y hy]

theorem tableauInsert_fixed_length {d : ℕ} (T : List (RowContent d)) (x : Fin d)
    (h : T.length = d) : (tableauInsert T x).1.length = d := by
  rw [tableauInsert_length_of_bound T x (by omega), h]

theorem pairwise_interlaces_cons {d : ℕ} {U V : RowContent d}
    {T : List (RowContent d)} (hUV : RowInterlaces U V)
    (hT : List.Pairwise RowInterlaces (V :: T)) :
    List.Pairwise RowInterlaces (U :: V :: T) := by
  rw [List.pairwise_cons]
  refine ⟨?_, hT⟩
  intro W hW
  rcases List.mem_cons.mp hW with rfl | hW
  · exact hUV
  · exact hUV.trans ((List.pairwise_cons.mp hT).1 W hW)

theorem tableauInsert_pairwise {d : ℕ} (T : List (RowContent d))
    (hT : List.Pairwise RowInterlaces T) (x : Fin d) :
    List.Pairwise RowInterlaces (tableauInsert T x).1 := by
  induction T generalizing x with
  | nil => simp [tableauInsert]
  | cons U T ih =>
    obtain ⟨hU, hT⟩ := List.pairwise_cons.mp hT
    cases hb : rowBump U x with
    | none =>
      simp only [tableauInsert, hb]
      exact List.pairwise_cons.mpr ⟨fun V hV => (hU V hV).insert_upper x, hT⟩
    | some y =>
      simp only [tableauInsert, hb]
      cases T with
      | nil =>
        simp only [tableauInsert]
        exact pairwise_interlaces_cons (RowInterlaces.insert_new_row U x y hb)
          (List.pairwise_singleton _ _)
      | cons V R =>
        have hUV := hU V (List.mem_cons_self)
        obtain ⟨S, hS⟩ := tableauInsert_cons_head V R y
        have hp := ih hT y
        rw [hS] at hp ⊢
        exact pairwise_interlaces_cons (hUV.insert_bumped x y hb) hp

theorem tableauInsert_content {d : ℕ} (T : List (RowContent d)) (x j : Fin d) :
    tableauContent (tableauInsert T x).1 j =
      tableauContent T j + if j = x then 1 else 0 := by
  induction T generalizing x with
  | nil => simp [tableauInsert, rowAdd_content]
  | cons U T ih =>
    cases hb : rowBump U x with
    | none => simp [tableauInsert, hb, rowInserted, rowAdd_content, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]
    | some y =>
      obtain ⟨hxy, hy, _⟩ := (rowBump_eq_some_iff U x y).mp hb
      have he := rowReplace_content U x y j (ne_of_lt hxy) hy
      simp only [tableauInsert, hb, tableauContent_cons, rowInserted]
      rw [ih y]
      omega

theorem tableauInsert_shape {d : ℕ} (T : List (RowContent d)) (x : Fin d) :
    tableauShape (tableauInsert T x).1 =
      shapeAdd (tableauShape T) (tableauInsert T x).2 := by
  induction T generalizing x with
  | nil => simp [tableauInsert, tableauShape, rowMass, rowAdd_mass, shapeAdd]
  | cons U T ih =>
    cases hb : rowBump U x with
    | none => simp [tableauInsert, hb, tableauShape, rowMass, rowInserted,
        rowAdd_mass, shapeAdd]
    | some y =>
      obtain ⟨hxy, hy, _⟩ := (rowBump_eq_some_iff U x y).mp hb
      have he := rowReplace_mass U x y (ne_of_lt hxy) hy
      simp only [tableauInsert, hb, tableauShape, List.map_cons, shapeAdd,
        rowInserted]
      change rowMass (rowReplace U x y) :: tableauShape (tableauInsert T y).1 = _
      rw [show rowMass (rowReplace U x y) = rowMass U from he, ih y]
      rfl

def tableauMonomial {d : ℕ} (p : Fin d → ℝ) (T : List (RowContent d)) : ℝ :=
  ∏ j, p j ^ tableauContent T j

/-- Exact insertion weight identity, valid even when some probabilities vanish. -/
theorem tableauInsert_monomial {d : ℕ} (p : Fin d → ℝ)
    (T : List (RowContent d)) (x : Fin d) :
    tableauMonomial p (tableauInsert T x).1 = tableauMonomial p T * p x := by
  simp only [tableauMonomial, tableauInsert_content, pow_add, Finset.prod_mul_distrib]
  simp

end Cloning.YoungGeneral
