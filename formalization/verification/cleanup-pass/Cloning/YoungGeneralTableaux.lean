import Cloning.YoungGeneralConcentration

/-!
# The general tableau formula and polynomial domination

A standard tableau is encoded by the row containing each successive box: its
prefix row counts are decreasing.  A semistandard tableau is encoded by the
number of each letter in each row.  Weak row order makes this encoding unique;
the prefix inequalities below express strict column order.  The formula
`standardCount * schurPolynomial` is consequently explicit and finite.

This file proves its concentration without assuming any bound on the Young
law.  It does not construct Schur--Weyl representation spaces or a Schur
measurement; that physical identification is a separate obligation.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace Cloning.YoungGeneral

/-- The prefix condition for the row word of a standard Young tableau. -/
def IsStandardWord {d N : ℕ} (w : Fin N → Fin d) : Prop :=
  ∀ n : ℕ, Antitone (fun i ↦ (Finset.univ.filter (fun k ↦ k.val < n ∧ w k = i)).card)

theorem standardWord_rows_antitone {d N : ℕ} (w : Fin N → Fin d)
    (hw : IsStandardWord w) : Antitone (rowCount w) := by
  have h := hw N
  simpa only [Fin.is_lt, true_and, rowCount] using h

theorem rowCount_le_length {d N : ℕ} (w : Fin N → Fin d) (i : Fin d) :
    rowCount w i ≤ N := by
  exact (Finset.card_filter_le ..).trans_eq (Fintype.card_fin N)

/-- A finite type containing every shape of an `N`-box diagram. -/
abbrev Shape (d N : ℕ) := Fin d → Fin (N + 1)

def wordShape {d N : ℕ} (w : Fin N → Fin d) : Shape d N :=
  fun i ↦ ⟨rowCount w i, Nat.lt_succ_of_le (rowCount_le_length w i)⟩

@[simp] theorem wordShape_val {d N : ℕ} (w : Fin N → Fin d) (i : Fin d) :
    (wordShape w i).val = rowCount w i := rfl

theorem wordShape_eq_iff {d N : ℕ} (w : Fin N → Fin d) (μ : Shape d N) :
    wordShape w = μ ↔ rowCount w = fun i ↦ (μ i).val := by
  constructor
  · intro h
    funext i
    exact congrArg Fin.val (congrFun h i)
  · intro h
    funext i
    exact Fin.ext (congrFun h i)

/-- Row-content arrays: the bound on each entry follows from the total number
of boxes. -/
abbrev ContentArray (d N : ℕ) := Fin d → Fin d → Fin (N + 1)

/-- Literal semistandard row-content conditions.  The second condition is the
usual consequence that every entry in row `i` is at least `i`. -/
def IsSemistandardContent {d N : ℕ} (μ : Fin d → ℕ) (A : ContentArray d N) : Prop :=
  (∀ i, ∑ j, (A i j).val = μ i) ∧
  (∀ i j, j < i → (A i j).val = 0) ∧
  (∀ i i' k, i < i' →
    (∑ j ∈ Finset.univ.filter (fun j ↦ j ≤ k), (A i' j).val) ≤
      ∑ j ∈ Finset.univ.filter (fun j ↦ j < k), (A i j).val)

def contentWeight {d N : ℕ} (p : Fin d → ℝ) (A : ContentArray d N) : ℝ :=
  ∏ i, ∏ j, p j ^ (A i j).val

def schurPolynomial {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (μ : Fin d → ℕ) : ℝ :=
  ∑ A : ContentArray d N, if IsSemistandardContent μ A then contentWeight p A else 0

def standardCount {d : ℕ} (N : ℕ) (μ : Fin d → ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin N → Fin d ↦ IsStandardWord w ∧ rowCount w = μ)).card

/-- The concrete standard-tableau times Schur-polynomial formula. -/
def youngWeight {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (μ : Fin d → ℕ) : ℝ :=
  (standardCount N μ : ℝ) * schurPolynomial N p μ

/-- The same formula before aggregating standard tableaux by final shape. -/
def standardWordWeight {d N : ℕ} (p : Fin d → ℝ) (w : Fin N → Fin d) : ℝ :=
  if IsStandardWord w then schurPolynomial N p (rowCount w) else 0

theorem contentWeight_nonneg {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (A : ContentArray d N) : 0 ≤ contentWeight p A :=
  Finset.prod_nonneg (fun i _ ↦ Finset.prod_nonneg (fun j _ ↦ pow_nonneg (hp j) _))

/-- Highest-weight domination, including spectra with repeated or zero entries. -/
theorem contentWeight_le_highest {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (horder : Antitone p)
    (μ : Fin d → ℕ) (A : ContentArray d N) (hA : IsSemistandardContent μ A) :
    contentWeight p A ≤ ∏ i, p i ^ μ i := by
  unfold contentWeight
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.prod_nonneg (fun j _ ↦ pow_nonneg (hp j) _)
  · intro i _
    calc
      _ ≤ ∏ j, p i ^ (A i j).val := by
        apply Finset.prod_le_prod (fun j _ ↦ pow_nonneg (hp j) _)
        intro j _
        by_cases hji : j < i
        · simp [hA.2.1 i j hji]
        · exact pow_le_pow_left₀ (hp j) (horder (le_of_not_gt hji)) _
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, hA.1 i]

theorem schurPolynomial_nonneg {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (μ : Fin d → ℕ) : 0 ≤ schurPolynomial N p μ := by
  apply Finset.sum_nonneg
  intro A _
  split_ifs
  · exact contentWeight_nonneg p hp A
  · exact le_rfl

/-- A deliberately loose polynomial dimension bound is sufficient for
concentration and needs no hook or Weyl dimension formula. -/
theorem schurPolynomial_le {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (horder : Antitone p) (μ : Fin d → ℕ) :
    schurPolynomial N p μ ≤ ((N : ℝ) + 1) ^ (d * d) * (∏ i, p i ^ μ i) := by
  classical
  calc
    _ ≤ ∑ _A : ContentArray d N, ∏ i, p i ^ μ i := by
      apply Finset.sum_le_sum
      intro A _
      split_ifs with hA
      · exact contentWeight_le_highest p hp horder μ A hA
      · exact Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hp i) _)
    _ = _ := by simp [ContentArray, Fintype.card_fun, ← pow_mul]

theorem standardWordWeight_nonneg {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (w : Fin N → Fin d) : 0 ≤ standardWordWeight p w := by
  unfold standardWordWeight
  split_ifs
  · exact schurPolynomial_nonneg N p hp _
  · exact le_rfl

/-- Actual tableau weights are dominated by a polynomial times IID word
weights.  There is no concentration or character bound among the premises. -/
theorem standardWordWeight_le {d N : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (horder : Antitone p) (w : Fin N → Fin d) :
    standardWordWeight p w ≤ ((N : ℝ) + 1) ^ (d * d) * wordWeight p w := by
  unfold standardWordWeight
  split_ifs
  · rw [wordWeight_eq_row_product]
    exact schurPolynomial_le N p hp horder _
  · exact mul_nonneg (by positivity) (wordWeight_nonneg p hp w)

/-- Grouping standard words by shape recovers the literal `f^μ s_μ(p)`
formula. -/
theorem sum_standardWordWeight_shape {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (μ : Fin d → ℕ) :
    (∑ w : Fin N → Fin d, if rowCount w = μ then standardWordWeight p w else 0) =
      youngWeight N p μ := by
  classical
  have hpoint (w : Fin N → Fin d) :
      (if rowCount w = μ then standardWordWeight p w else 0) =
        if IsStandardWord w ∧ rowCount w = μ then schurPolynomial N p μ else 0 := by
    unfold standardWordWeight
    split_ifs <;> simp_all
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [youngWeight, standardCount]

/-- Exact change from tableau row words to the finite space of shape vectors. -/
theorem sum_youngWeight_mul {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (f : Shape d N → ℝ) :
    (∑ μ : Shape d N, youngWeight N p (fun i ↦ (μ i).val) * f μ) =
      ∑ w : Fin N → Fin d, standardWordWeight p w * f (wordShape w) := by
  classical
  simp_rw [← sum_standardWordWeight_shape]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [← wordShape_eq_iff, ite_mul, zero_mul]
  simp

theorem youngWeight_nonneg {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (μ : Fin d → ℕ) : 0 ≤ youngWeight N p μ :=
  mul_nonneg (Nat.cast_nonneg _) (schurPolynomial_nonneg N p hp μ)

/-- Nonzero tableau mass can occur only at actual decreasing partitions of N. -/
theorem youngWeight_support {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (μ : Fin d → ℕ) (h : youngWeight N p μ ≠ 0) :
    Antitone μ ∧ ∑ i, μ i = N := by
  classical
  have hc : standardCount N μ ≠ 0 := by
    intro he
    apply h
    simp [youngWeight, he]
  obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hc
  obtain ⟨_, hw, he⟩ := Finset.mem_filter.mp hw
  exact ⟨he ▸ standardWord_rows_antitone w hw, he ▸ sum_rowCount w⟩

/-- Atypical mass calculated directly from the standard/semistandard formula. -/
def atypicalMass {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (ε : ℝ) : ℝ :=
  ∑ w : Fin N → Fin d,
    if ∃ i, (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then standardWordWeight p w else 0

theorem atypicalMass_nonneg {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (ε : ℝ) : 0 ≤ atypicalMass N p ε := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact standardWordWeight_nonneg p hp w
  · exact le_rfl

/-- General-rank Young concentration from the actual finite tableau formula.
It is uniform on the entire closed ordered probability simplex. -/
theorem atypicalMass_le {d : ℕ} (N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (horder : Antitone p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    atypicalMass N p ε ≤
      ((N : ℝ) + 1) ^ (d * d) * (2 * d * Real.exp (-(N : ℝ) * ε ^ 2 / 4)) := by
  classical
  calc
    _ ≤ ∑ w : Fin N → Fin d, ((N : ℝ) + 1) ^ (d * d) *
        (if ∃ i, (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0) := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact standardWordWeight_le p hp horder w
      · simp
    _ = ((N : ℝ) + 1) ^ (d * d) * (∑ w : Fin N → Fin d,
        if ∃ i, (N : ℝ) * ε ≤ |(rowCount w i : ℝ) - N * p i| then wordWeight p w else 0) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_rowCount_tail_le p hp hs ε hε hε2) (by positivity)

end Cloning.YoungGeneral
