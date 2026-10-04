import Cloning.YoungBranchingStandard

/-!
# Intrinsic finite tableau sums and independence of the storage bound

The entries of the concrete row-content arrays are stored in `Fin (N+1)`.
Every semistandard array is automatically bounded by its row lengths, so this
storage parameter does not change the Schur polynomial once it contains the
shape.  We prove the actual equivalence of admissible arrays, preserving every
monomial, rather than postulating polynomial stability.
-/

noncomputable section
open scoped BigOperators Classical

namespace Cloning.YoungGeneral

abbrev SemistandardContent {d : ℕ} (N : ℕ) (μ : Fin d → ℕ) :=
  {A : ContentArray d N // IsSemistandardContent μ A}

theorem content_entry_le_row {d N : ℕ} {μ : Fin d → ℕ} (A : SemistandardContent N μ)
    (i j : Fin d) : (A.val i j).val ≤ μ i := by
  rw [← A.property.1 i]
  exact Finset.single_le_sum (f := fun k ↦ (A.val i k).val)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)

/-- Re-encode an actual admissible tableau in any sufficient entry bound. -/
def rebaseContent {d N : ℕ} {μ : Fin d → ℕ} (A : SemistandardContent N μ)
    (M : ℕ) (hM : ∀ i, μ i ≤ M) : SemistandardContent M μ := by
  let B : ContentArray d M := fun i j ↦
    ⟨(A.val i j).val, Nat.lt_succ_of_le ((content_entry_le_row A i j).trans (hM i))⟩
  refine ⟨B, ?_⟩
  exact A.property

@[simp] theorem rebaseContent_val {d N : ℕ} {μ : Fin d → ℕ}
    (A : SemistandardContent N μ) (M : ℕ) (hM : ∀ i, μ i ≤ M) (i j : Fin d) :
    ((rebaseContent A M hM).val i j).val = (A.val i j).val := rfl

def rebaseContentEquiv {d : ℕ} (N M : ℕ) (μ : Fin d → ℕ)
    (hN : ∀ i, μ i ≤ N) (hM : ∀ i, μ i ≤ M) :
    SemistandardContent N μ ≃ SemistandardContent M μ where
  toFun A := rebaseContent A M hM
  invFun A := rebaseContent A N hN
  left_inv A := by
    apply Subtype.ext
    funext i j
    apply Fin.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    funext i j
    apply Fin.ext
    rfl

theorem contentWeight_rebase {d N : ℕ} {μ : Fin d → ℕ} (p : Fin d → ℝ)
    (A : SemistandardContent N μ) (M : ℕ) (hM : ∀ i, μ i ≤ M) :
    contentWeight p (rebaseContent A M hM).val = contentWeight p A.val := rfl

theorem schurPolynomial_eq_content_sum {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (μ : Fin d → ℕ) :
    schurPolynomial N p μ = ∑ A : SemistandardContent N μ, contentWeight p A.val := by
  unfold schurPolynomial
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The Schur polynomial depends on the tableau shape, not its entry-bound
implementation parameter. -/
theorem schurPolynomial_rebase {d : ℕ} (N M : ℕ) (p : Fin d → ℝ) (μ : Fin d → ℕ)
    (hN : ∀ i, μ i ≤ N) (hM : ∀ i, μ i ≤ M) :
    schurPolynomial N p μ = schurPolynomial M p μ := by
  rw [schurPolynomial_eq_content_sum, schurPolynomial_eq_content_sum]
  exact (rebaseContentEquiv N M μ hN hM).sum_comp (fun A ↦ contentWeight p A.val)

theorem row_le_sum {d : ℕ} (μ : Fin d → ℕ) (i : Fin d) : μ i ≤ ∑ j, μ j :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- Stability at a fixed box count, in the form required by the normalization
induction's `N` to `N+1` step. -/
theorem schurPolynomial_succ_of_boxes {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (μ : Fin d → ℕ) (hμ : ∑ i, μ i = N) :
    schurPolynomial N p μ = schurPolynomial (N + 1) p μ := by
  have hb i : μ i ≤ N := by simpa [hμ] using row_le_sum μ i
  exact schurPolynomial_rebase N (N + 1) p μ hb (fun i ↦ (hb i).trans (by omega))

theorem content_total_degree {d N : ℕ} {μ : Fin d → ℕ} (A : SemistandardContent N μ) :
    (∑ i, ∑ j, (A.val i j).val) = ∑ i, μ i := by
  simp_rw [A.property.1]

/-- Exact degree of each concrete tableau monomial. -/
theorem contentWeight_smul {d N : ℕ} {μ : Fin d → ℕ} (p : Fin d → ℝ)
    (A : SemistandardContent N μ) (c : ℝ) :
    contentWeight (fun i ↦ c * p i) A.val = c ^ (∑ i, μ i) * contentWeight p A.val := by
  unfold contentWeight
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [content_total_degree]

/-- Homogeneity is derived term by term from the actual tableau contents. -/
theorem schurPolynomial_homogeneous {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (μ : Fin d → ℕ) (c : ℝ) :
    schurPolynomial N (fun i ↦ c * p i) μ = c ^ (∑ i, μ i) * schurPolynomial N p μ := by
  rw [schurPolynomial_eq_content_sum, schurPolynomial_eq_content_sum]
  simp_rw [contentWeight_smul]
  exact (Finset.mul_sum ..).symm

end Cloning.YoungGeneral
