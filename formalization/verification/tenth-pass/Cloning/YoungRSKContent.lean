import Cloning.YoungRSKTableau
import Cloning.YoungBranchingContent
import Mathlib.Data.List.OfFn

/-!
# Literal finite arrays and count-row tableaux

The triangular zero condition is a consequence of strict-column interlacing.
This file connects the list representation used by insertion with the finite
content arrays used in the Schur polynomial.
-/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

theorem row_entry_le_prefix {d : ℕ} (A : RowContent d) (j : Fin d) :
    A j ≤ rowPrefix A j := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

/-- Strict columns force row `i` to contain only letters at least `i`. -/
theorem row_array_triangular_of_interlacing {d : ℕ} (A : Fin d → RowContent d)
    (hA : ∀ i j, i < j → RowInterlaces (A i) (A j)) :
    ∀ i j, j < i → A i j = 0 := by
  suffices h : ∀ n, ∀ i : Fin d, i.val = n → ∀ j, j < i → A i j = 0 by
    intro i j hj
    exact h i.val i rfl j hj
  intro n
  induction n with
  | zero => intro i hi j hj; have : j.val < i.val := hj; omega
  | succ n ih =>
    intro i hi j hj
    have hnd : n < d := by omega
    let prev : Fin d := ⟨n, hnd⟩
    have hp : prev < i := by change n < i.val; omega
    have hs : rowStrictPrefix (A prev) j = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk : k < j := (Finset.mem_filter.mp hk).2
      exact ih prev rfl k (by change k.val < n; have : j.val < i.val := hj; omega)
    have hbound := (row_entry_le_prefix (A i) j).trans (hA prev i hp j)
    rw [hs] at hbound
    exact Nat.eq_zero_of_le_zero hbound

def contentRows {d N : ℕ} (A : ContentArray d N) : List (RowContent d) :=
  List.ofFn (fun i => fun j => (A i j).val)

@[simp] theorem contentRows_length {d N : ℕ} (A : ContentArray d N) :
    (contentRows A).length = d := by simp [contentRows]

theorem contentRows_pairwise {d N : ℕ} {μ : Fin d → ℕ}
    (A : SemistandardContent N μ) : List.Pairwise RowInterlaces (contentRows A.val) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact semistandardContent_rowInterlaces A.property i j hij

theorem contentRows_shape {d N : ℕ} {μ : Fin d → ℕ}
    (A : SemistandardContent N μ) : tableauShape (contentRows A.val) = List.ofFn μ := by
  simp only [tableauShape, contentRows, List.map_ofFn]
  congr 1
  funext i
  exact A.property.1 i

theorem contentRows_injective {d N : ℕ} :
    Function.Injective (@contentRows d N) := by
  intro A B h
  have he : (fun i j => (A i j).val) = (fun i j => (B i j).val) :=
    List.ofFn_injective h
  funext i j
  exact Fin.ext (congrFun (congrFun he i) j)

theorem contentRows_monomial {d N : ℕ} (p : Fin d → ℝ) (A : ContentArray d N) :
    tableauMonomial p (contentRows A) = contentWeight p A := by
  simp only [tableauMonomial, tableauContent, contentRows, List.map_ofFn, List.sum_ofFn]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_comm

theorem shapeAdd_ofFn {d : ℕ} (μ : Fin d → ℕ) (r : Fin d) :
    shapeAdd (List.ofFn μ) r.val = List.ofFn (addBox μ r) := by
  induction d with
  | zero => exact Fin.elim0 r
  | succ d ih =>
    refine Fin.cases ?_ (fun s => ?_) r
    · simp [List.ofFn_succ, shapeAdd, addBox]
    · simp only [List.ofFn_succ, Fin.val_succ, shapeAdd]
      rw [ih]
      simp [addBox]
      exact ⟨(Fin.succ_ne_zero s).symm, rfl⟩

def rowsArray {d : ℕ} (T : List (RowContent d)) (hT : T.length = d) :
    Fin d → RowContent d := fun i => T.get ⟨i.val, by omega⟩

theorem rowsArray_ofFn {d : ℕ} (A : Fin d → RowContent d) :
    rowsArray (List.ofFn A) List.length_ofFn = A := by
  funext i
  simp [rowsArray]

theorem ofFn_rowsArray {d : ℕ} (T : List (RowContent d)) (hT : T.length = d) :
    List.ofFn (rowsArray T hT) = T := by
  apply List.ext_get (by simpa using hT.symm)
  intro n h₁ h₂
  simp [rowsArray]

theorem rowsArray_shape {d : ℕ} {T : List (RowContent d)} {μ : Fin d → ℕ}
    (hT : T.length = d) (hμ : tableauShape T = List.ofFn μ) (i : Fin d) :
    rowMass (rowsArray T hT i) = μ i := by
  have he : List.ofFn (fun i => rowMass (rowsArray T hT i)) = List.ofFn μ := by
    change List.ofFn (rowMass ∘ rowsArray T hT) = _
    rw [← List.map_ofFn, ofFn_rowsArray]
    exact hμ
  exact congrFun (List.ofFn_injective he) i

theorem rowsArray_pairwise {d : ℕ} {T : List (RowContent d)}
    (hT : T.length = d) (hp : List.Pairwise RowInterlaces T) :
    ∀ i j, i < j → RowInterlaces (rowsArray T hT i) (rowsArray T hT j) := by
  have he : List.Pairwise RowInterlaces (List.ofFn (rowsArray T hT)) := by
    rwa [ofFn_rowsArray]
  exact fun _ _ h => List.pairwise_ofFn.mp he h

def rowsContent {d N : ℕ} (T : List (RowContent d)) (hT : T.length = d)
    (hb : ∀ i j, rowsArray T hT i j ≤ N) : ContentArray d N :=
  fun i j => ⟨rowsArray T hT i j, Nat.lt_succ_of_le (hb i j)⟩

theorem rowsContent_rows {d N : ℕ} (T : List (RowContent d)) (hT : T.length = d)
    (hb : ∀ i j, rowsArray T hT i j ≤ N) :
    contentRows (rowsContent T hT hb) = T :=
  ofFn_rowsArray T hT

/-- Any interlacing count-row tableau with bounded row sizes gives one of the
literal finite arrays appearing in the Schur sum. -/
def rowsSemistandardContent {d N : ℕ} {μ : Fin d → ℕ}
    (T : List (RowContent d)) (hT : T.length = d)
    (hμ : tableauShape T = List.ofFn μ) (hp : List.Pairwise RowInterlaces T)
    (hN : ∀ i, μ i ≤ N) : SemistandardContent N μ := by
  have hmass := rowsArray_shape hT hμ
  have hb : ∀ i j, rowsArray T hT i j ≤ N := by
    intro i j
    apply le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
    exact (hmass i).le.trans (hN i)
  refine ⟨rowsContent T hT hb, ?_, ?_, ?_⟩
  · exact hmass
  · exact row_array_triangular_of_interlacing _ (rowsArray_pairwise hT hp)
  · exact fun i j k hij => rowsArray_pairwise hT hp i j hij k

theorem rowsSemistandardContent_rows {d N : ℕ} {μ : Fin d → ℕ}
    (T : List (RowContent d)) (hT : T.length = d)
    (hμ : tableauShape T = List.ofFn μ) (hp : List.Pairwise RowInterlaces T)
    (hN : ∀ i, μ i ≤ N) :
    contentRows (rowsSemistandardContent T hT hμ hp hN).val = T :=
  ofFn_rowsArray T hT

def contentInsertCorner {d N : ℕ} {μ : Fin d → ℕ}
    (A : SemistandardContent N μ) (x : Fin d) : Fin d :=
  ⟨(tableauInsert (contentRows A.val) x).2, by
    have he := tableauInsert_fixed_length (contentRows A.val) x (contentRows_length A.val)
    have ht := tableauInsert_corner_lt (contentRows A.val) x
    omega⟩

/-- Genuine RSK insertion on the exact bounded arrays of the Schur sum. -/
def contentInsert {d N : ℕ} {μ : Fin d → ℕ} (A : SemistandardContent N μ)
    (hN : ∀ i, μ i ≤ N) (x : Fin d) :
    SemistandardContent (N + 1) (addBox μ (contentInsertCorner A x)) :=
  rowsSemistandardContent (tableauInsert (contentRows A.val) x).1
    (tableauInsert_fixed_length _ x (contentRows_length _))
    (by rw [tableauInsert_shape, contentRows_shape]
        exact shapeAdd_ofFn μ (contentInsertCorner A x))
    (tableauInsert_pairwise _ (contentRows_pairwise A) x)
    (fun i => by have := hN i; simp only [addBox]; split_ifs <;> omega)

theorem contentInsert_rows {d N : ℕ} {μ : Fin d → ℕ} (A : SemistandardContent N μ)
    (hN : ∀ i, μ i ≤ N) (x : Fin d) :
    contentRows (contentInsert A hN x).val = (tableauInsert (contentRows A.val) x).1 :=
  rowsSemistandardContent_rows _ _ _ _ _

theorem contentInsert_weight {d N : ℕ} {μ : Fin d → ℕ} (p : Fin d → ℝ)
    (A : SemistandardContent N μ) (hN : ∀ i, μ i ≤ N) (x : Fin d) :
    contentWeight p (contentInsert A hN x).val = contentWeight p A.val * p x := by
  rw [← contentRows_monomial, contentInsert_rows, tableauInsert_monomial,
    contentRows_monomial]

end Cloning.YoungGeneral
