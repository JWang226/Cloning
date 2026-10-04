import Cloning.YoungRSKShape
import Cloning.YoungRSKTableauReverse

/-!
# The actual weighted one-box Pieri bijection

Literal row insertion and reverse deletion identify a tableau with one input
letter with all one-box successor tableaux. No normalization or existence of
a Young probability law is assumed.
-/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

theorem tableauRemovable_iff_shape {d : ℕ} (T : List (RowContent d)) (r : ℕ) :
    tableauRemovable T r ↔ shapeRemovable (tableauShape T) r := by
  induction T generalizing r with
  | nil => simp [tableauRemovable, tableauShape, shapeRemovable]
  | cons U T ih =>
    cases r with
    | zero =>
      cases T <;> simp [tableauRemovable, tableauShape, shapeRemovable, rowMass]
    | succ r => exact ih r

theorem semistandardContent_antitone {d N : ℕ} {μ : Fin d → ℕ}
    (A : SemistandardContent N μ) : Antitone μ := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · rfl
  · have h := rowInterlaces_mass_le (fun k => (A.val i k).val)
      (fun k => (A.val j k).val) (semistandardContent_rowInterlaces A.property i j hij)
    simpa only [A.property.1] using h

theorem schurPolynomial_eq_zero_of_not_antitone {d : ℕ} (N : ℕ)
    (p : Fin d → ℝ) (μ : Fin d → ℕ) (hμ : ¬ Antitone μ) :
    schurPolynomial N p μ = 0 := by
  rw [schurPolynomial_eq_content_sum]
  apply Finset.sum_eq_zero
  intro A _
  exact (hμ (semistandardContent_antitone A)).elim

abbrev ContentSuccessor {d : ℕ} (N : ℕ) (μ : Fin d → ℕ) :=
  Σ r : Fin d, SemistandardContent (N + 1) (addBox μ r)

def contentInsertion {d N : ℕ} (μ : Fin d → ℕ) (hN : ∀ i, μ i ≤ N) :
    SemistandardContent N μ × Fin d → ContentSuccessor N μ :=
  fun z => ⟨contentInsertCorner z.1 z.2, contentInsert z.1 hN z.2⟩

theorem contentInsertion_injective {d N : ℕ} (μ : Fin d → ℕ) (hN : ∀ i, μ i ≤ N) :
    Function.Injective (contentInsertion μ hN) := by
  rintro ⟨A, x⟩ ⟨B, y⟩ he
  have hc := congrArg (fun z : ContentSuccessor N μ => z.1.val) he
  have hr := congrArg (fun z : ContentSuccessor N μ => contentRows z.2.val) he
  change (contentInsertCorner A x).val = (contentInsertCorner B y).val at hc
  change contentRows (contentInsert A hN x).val = contentRows (contentInsert B hN y).val at hr
  rw [contentInsert_rows, contentInsert_rows] at hr
  have ha := tableauReverse_after_insert_fixed (contentRows A.val) x (contentRows_length _)
  have hb := tableauReverse_after_insert_fixed (contentRows B.val) y (contentRows_length _)
  change (tableauInsert (contentRows A.val) x).2 =
    (tableauInsert (contentRows B.val) y).2 at hc
  rw [hr, hc] at ha
  have hp := Option.some.inj (ha.symm.trans hb)
  have hAB : A = B := Subtype.ext (contentRows_injective (congrArg Prod.fst hp))
  exact Prod.ext hAB (congrArg (fun z : List (RowContent d) × Fin d => z.2) hp)

theorem contentInsertion_surjective {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∀ i, μ i ≤ N) :
    Function.Surjective (contentInsertion μ hN) := by
  rintro ⟨r, B⟩
  have hrem : tableauRemovable (contentRows B.val) r.val := by
    rw [tableauRemovable_iff_shape, contentRows_shape]
    exact shapeRemovable_addBox μ hμ r
  obtain ⟨S, x, hrev, hp⟩ := tableauReverse_exists_pairwise (contentRows B.val)
    (contentRows_pairwise B) r.val hrem
  have hlen : S.length = d :=
    (tableauReverse_length _ _ _ _ hrev).trans (contentRows_length _)
  have hshape : tableauShape S = List.ofFn μ := by
    apply shapeAdd_injective_of_length (r := r.val)
    · simpa only [tableauShape, List.length_map, List.length_ofFn] using hlen
    · rw [tableauReverse_shape _ _ _ _ hrev, contentRows_shape, shapeAdd_ofFn]
  let A := rowsSemistandardContent S hlen hshape hp hN
  have hA : contentRows A.val = S := rowsSemistandardContent_rows _ _ _ _ _
  have hins : tableauInsert (contentRows A.val) x = (contentRows B.val, r.val) := by
    rw [hA]
    exact tableauInsert_after_reverse _ _ _ _ hrev
  have hcorner : contentInsertCorner A x = r := Fin.ext (congrArg Prod.snd hins)
  refine ⟨(A, x), ?_⟩
  apply Sigma.ext hcorner
  have hrows : contentRows (contentInsert A hN x).val = contentRows B.val := by
    rw [contentInsert_rows]
    exact congrArg Prod.fst hins
  have hval := contentRows_injective hrows
  exact (Subtype.heq_iff_coe_eq (fun _ => by
    change IsSemistandardContent (addBox μ (contentInsertCorner A x)) _ ↔
      IsSemistandardContent (addBox μ r) _
    rw [hcorner])).mpr hval

def contentInsertionEquiv {d N : ℕ} (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∀ i, μ i ≤ N) :
    (SemistandardContent N μ × Fin d) ≃ ContentSuccessor N μ :=
  Equiv.ofBijective (contentInsertion μ hN)
    ⟨contentInsertion_injective μ hN, contentInsertion_surjective μ hμ hN⟩

/-- Exact weighted Pieri identity for the literal finite-array Schur sum. -/
theorem schurPolynomial_pieri {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (μ : Fin d → ℕ)
    (hμ : Antitone μ) (hN : ∀ i, μ i ≤ N) :
    (∑ i : Fin d, schurPolynomial (N + 1) p (addBox μ i)) =
      schurPolynomial N p μ * ∑ i, p i := by
  simp only [schurPolynomial_eq_content_sum]
  rw [← Fintype.sum_sigma (fun z : ContentSuccessor N μ => contentWeight p z.2.val)]
  rw [← (contentInsertionEquiv μ hμ hN).sum_comp]
  change (∑ z : SemistandardContent N μ × Fin d,
    contentWeight p (contentInsert z.1 hN z.2).val) = _
  simp only [contentInsert_weight, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  exact (Finset.sum_mul _ _ _).symm

end Cloning.YoungGeneral
