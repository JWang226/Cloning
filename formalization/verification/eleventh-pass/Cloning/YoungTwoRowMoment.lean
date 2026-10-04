import Cloning.Projector
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

/-!
# A concrete two-row Young law and its exact Casimir moment

Paths add one box to either of two rows; a path is legal when the upper row
never becomes shorter than the lower row. Each legal path has weight
`(row gap + 1) / 2^N`. Thus the marginal of a fixed shape is its number of
standard two-row tableau paths times its two-letter Schur dimension, divided
by `2^N`. Normalization and the moment estimates are proved from the explicit
branching probabilities, not assumed as distributional identities.

This combinatorial construction does not assert an identification with
particular irreducible representation spaces.
-/

noncomputable section
open scoped BigOperators

namespace Cloning.YoungTwoRow

/-- Binary histories of length `N`, with the most recent choice at the end. -/
def Path : ℕ → Type
  | 0 => Unit
  | N + 1 => Path N × Bool

instance pathFintype : (N : ℕ) → Fintype (Path N)
  | 0 => inferInstanceAs (Fintype Unit)
  | N + 1 =>
    letI := pathFintype N
    inferInstanceAs (Fintype (Path N × Bool))

def stepSpin (s : ℕ) (b : Bool) : ℕ := if b then s + 1 else s - 1

/-- The exact dimension-ratio branching probabilities for two rows. -/
def stepProbability (s : ℕ) (b : Bool) : ℝ :=
  if b then ((s : ℝ) + 2) / (2 * ((s : ℝ) + 1))
  else (s : ℝ) / (2 * ((s : ℝ) + 1))

def spin : (N : ℕ) → Path N → ℕ
  | 0, _ => 0
  | N + 1, p => stepSpin (spin N p.1) p.2

def weight : (N : ℕ) → Path N → ℝ
  | 0, _ => 1
  | N + 1, p => weight N p.1 * stepProbability (spin N p.1) p.2

def legal : (N : ℕ) → Path N → Prop
  | 0, _ => True
  | N + 1, p => legal N p.1 ∧ (p.2 = true ∨ 0 < spin N p.1)

instance legalDecidable (N : ℕ) (p : Path N) : Decidable (legal N p) :=
  Classical.propDecidable _

def upperRow : (N : ℕ) → Path N → ℕ
  | 0, _ => 0
  | N + 1, p => upperRow N p.1 + if p.2 then 1 else 0

def lowerRow : (N : ℕ) → Path N → ℕ
  | 0, _ => 0
  | N + 1, p => lowerRow N p.1 + if p.2 then 0 else 1

def spinCasimir (s : ℕ) : ℝ := (s : ℝ) * ((s : ℝ) + 2)

def expectation (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p : Path N, weight N p * f (spin N p)

theorem stepProbability_nonneg (s : ℕ) (b : Bool) : 0 ≤ stepProbability s b := by
  cases b <;> dsimp [stepProbability] <;> positivity

theorem stepProbability_sum (s : ℕ) : (∑ b : Bool, stepProbability s b) = 1 := by
  simp only [Fintype.sum_bool, stepProbability, Bool.false_eq_true, ↓reduceIte]
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem step_spinCasimir (s : ℕ) :
    (∑ b : Bool, stepProbability s b * spinCasimir (stepSpin s b)) =
      spinCasimir s + 3 := by
  cases s with
  | zero => norm_num [Fintype.sum_bool, stepProbability, stepSpin, spinCasimir]
  | succ s =>
    simp only [Fintype.sum_bool, stepProbability, stepSpin, spinCasimir,
      Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hs : (s : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem weight_nonneg (N : ℕ) (p : Path N) : 0 ≤ weight N p := by
  induction N with
  | zero => exact zero_le_one
  | succ N ih => exact mul_nonneg (ih p.1) (stepProbability_nonneg _ _)

/-- The elementary expectation recursion for this concrete finite law. -/
theorem expectation_succ (N : ℕ) (f : ℕ → ℝ) :
    expectation (N + 1) f = ∑ p : Path N, weight N p *
      ∑ b : Bool, stepProbability (spin N p) b * f (stepSpin (spin N p) b) := by
  change (∑ p : Path N × Bool, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp [weight, spin]
  ring

theorem expectation_one (N : ℕ) : expectation N (fun _ => 1) = 1 := by
  induction N with
  | zero => simp [expectation, weight, Path]
  | succ N ih =>
    rw [expectation_succ]
    simp only [mul_one, stepProbability_sum]
    simpa only [expectation, mul_one] using ih

/-- Normalization is a theorem about the explicit finite weights. -/
theorem weight_sum (N : ℕ) : (∑ p : Path N, weight N p) = 1 := by
  simpa only [expectation, mul_one] using expectation_one N

/-- The exact rank-two quadratic Casimir moment, without a moment premise. -/
theorem expectation_spinCasimir (N : ℕ) : expectation N spinCasimir = 3 * (N : ℝ) := by
  induction N with
  | zero => simp [expectation, weight, spin, spinCasimir, Path]
  | succ N ih =>
    rw [expectation_succ]
    simp_rw [step_spinCasimir, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [weight_sum]
    change expectation N spinCasimir + 1 * 3 = _
    rw [ih, Nat.cast_add, Nat.cast_one]
    ring

/-- The two row lengths contain exactly the number of boxes added. -/
theorem row_sum (N : ℕ) (p : Path N) : upperRow N p + lowerRow N p = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    obtain ⟨p, b⟩ := p
    have h := ih p
    cases b <;> simp only [upperRow, lowerRow, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- On legal tableaux the spin is exactly the ordered row gap. -/
theorem spin_add_lower_eq_upper (N : ℕ) (p : Path N) (hp : legal N p) :
    spin N p + lowerRow N p = upperRow N p := by
  induction N with
  | zero => rfl
  | succ N ih =>
    obtain ⟨p, b⟩ := p
    have h := ih p hp.1
    have hs := hp.2
    cases b with
    | false =>
      have hs0 : 0 < spin N p := by simpa using hs
      change (spin N p - 1) + (lowerRow N p + 1) = upperRow N p + 0
      omega
    | true =>
      change (spin N p + 1) + (lowerRow N p + 0) = upperRow N p + 1
      omega

theorem lowerRow_le_upperRow (N : ℕ) (p : Path N) (hp : legal N p) :
    lowerRow N p ≤ upperRow N p := by
  have := spin_add_lower_eq_upper N p hp
  omega

/-- The actual branching weights telescope to the Schur path weight.
Illegal histories have zero weight, including every attempted lower-row
extension when the two row lengths are equal. -/
theorem weight_formula (N : ℕ) (p : Path N) :
    weight N p = if legal N p then ((spin N p : ℝ) + 1) / (2 : ℝ) ^ N else 0 := by
  classical
  induction N with
  | zero => simp [weight, spin, legal]
  | succ N ih =>
    obtain ⟨p, b⟩ := p
    by_cases hp : legal N p
    · cases b with
      | false =>
        cases hs : spin N p with
        | zero => simp [weight, ih p, hp, hs, stepProbability, legal]
        | succ s =>
          have hd : (s : ℝ) + 1 + 1 ≠ 0 := by positivity
          simp only [weight, ih p, hp, hs, stepProbability, legal, spin, stepSpin,
            Bool.false_eq_true, false_or, Nat.succ_pos, and_self, ↓reduceIte,
            Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
          field_simp
      | true =>
        have hd : (spin N p : ℝ) + 1 ≠ 0 := by positivity
        simp only [weight, ih p, hp, stepProbability, legal, spin, stepSpin,
          true_or, and_self, ↓reduceIte, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp
        ring
    · simp [weight, ih p, hp, legal]

theorem weight_eq_zero_of_not_legal (N : ℕ) (p : Path N) (hp : ¬ legal N p) :
    weight N p = 0 := by rw [weight_formula]; simp [hp]

/-- The manuscript's Euclidean squared fluctuation of the actual two rows. -/
def rowVariance (N : ℕ) (p : Path N) : ℝ :=
  ((upperRow N p : ℝ) - (N : ℝ) / 2) ^ 2 +
    ((lowerRow N p : ℝ) - (N : ℝ) / 2) ^ 2

theorem rowVariance_eq_half_spin_sq (N : ℕ) (p : Path N) (hp : legal N p) :
    rowVariance N p = (spin N p : ℝ) ^ 2 / 2 := by
  have hsum : (upperRow N p : ℝ) + (lowerRow N p : ℝ) = N :=
    by exact_mod_cast row_sum N p
  have hgap : (spin N p : ℝ) + (lowerRow N p : ℝ) = upperRow N p :=
    by exact_mod_cast spin_add_lower_eq_upper N p hp
  dsimp [rowVariance]
  rw [← hsum, ← hgap]
  ring

/-- A concrete centered second-moment bound, with the manuscript's exact
rank-two constant `r − 1/r = 3/2`. No distribution or moment law is a premise. -/
theorem centered_second_moment_le (N : ℕ) :
    (∑ p : Path N, weight N p * rowVariance N p) ≤ 3 * (N : ℝ) / 2 := by
  have hp (p : Path N) : weight N p * rowVariance N p ≤
      weight N p * spinCasimir (spin N p) / 2 := by
    by_cases hl : legal N p
    · rw [rowVariance_eq_half_spin_sq N p hl]
      have hs : 0 ≤ (spin N p : ℝ) := Nat.cast_nonneg _
      have hw := weight_nonneg N p
      dsimp [spinCasimir]
      nlinarith [mul_nonneg hw hs]
    · rw [weight_eq_zero_of_not_legal N p hl]
      simp
  calc
    _ ≤ ∑ p : Path N, weight N p * spinCasimir (spin N p) / 2 :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = expectation N spinCasimir / 2 := by
      simp only [expectation, div_eq_mul_inv, ← Finset.sum_mul]
    _ = _ := by rw [expectation_spinCasimir]

/-- The exact two-row quadratic Casimir eigenvalue polynomial. -/
def rowCasimir (N : ℕ) (p : Path N) : ℝ :=
  (upperRow N p : ℝ) * ((upperRow N p : ℝ) + 1) +
    (lowerRow N p : ℝ) * ((lowerRow N p : ℝ) - 1)

theorem rowCasimir_eq (N : ℕ) (p : Path N) (hp : legal N p) :
    rowCasimir N p = (N : ℝ) ^ 2 / 2 + spinCasimir (spin N p) / 2 := by
  have hsum : (upperRow N p : ℝ) + (lowerRow N p : ℝ) = N :=
    by exact_mod_cast row_sum N p
  have hgap : (spin N p : ℝ) + (lowerRow N p : ℝ) = upperRow N p :=
    by exact_mod_cast spin_add_lower_eq_upper N p hp
  dsimp [rowCasimir, spinCasimir]
  rw [← hsum, ← hgap]
  ring

/-- The concrete law has exactly the Casimir expectation used in the
manuscript: `Nr + N(N−1)/r`, here with `r=2`. -/
theorem expectation_rowCasimir (N : ℕ) :
    (∑ p : Path N, weight N p * rowCasimir N p) =
      (N : ℝ) * 2 + (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  have hp (p : Path N) : weight N p * rowCasimir N p =
      weight N p * ((N : ℝ) ^ 2 / 2 + spinCasimir (spin N p) / 2) := by
    by_cases hl : legal N p
    · rw [rowCasimir_eq N p hl]
    · rw [weight_eq_zero_of_not_legal N p hl]
      simp
  simp_rw [hp, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [weight_sum]
  have hhalf : (∑ p : Path N, weight N p * (spinCasimir (spin N p) / 2)) =
      expectation N spinCasimir / 2 := by
    simp only [expectation, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  rw [hhalf, expectation_spinCasimir]
  ring

theorem spin_le_length (N : ℕ) (p : Path N) : spin N p ≤ N := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    obtain ⟨p, b⟩ := p
    have h := ih p
    cases b <;> simp only [spin, stepSpin, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The actual number of legal standard tableau paths ending at a given gap. -/
def tableauPathCount (N s : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Path N => legal N p ∧ spin N p = s)).card

/-- The shape marginal of the normalized finite path law. -/
def shapeProbability (N s : ℕ) : ℝ :=
  ∑ p : Path N, if spin N p = s then weight N p else 0

/-- The exact combinatorial Schur-weight formula: dimension `s+1` times
the actual tableau-path multiplicity, divided by `2^N`. -/
theorem shapeProbability_formula (N s : ℕ) :
    shapeProbability N s = ((s : ℝ) + 1) * tableauPathCount N s / (2 : ℝ) ^ N := by
  have hp (p : Path N) : (if spin N p = s then weight N p else 0) =
      if legal N p ∧ spin N p = s then ((s : ℝ) + 1) / (2 : ℝ) ^ N else 0 := by
    by_cases hs : spin N p = s <;> by_cases hl : legal N p <;>
      simp [hs, hl, weight_formula]
  unfold shapeProbability
  simp_rw [hp]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, tableauPathCount]
  ring

theorem shapeProbability_nonneg (N s : ℕ) : 0 ≤ shapeProbability N s := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact weight_nonneg N p
  · exact le_rfl

/-- Every expectation depending only on the shape agrees with its finite
shape marginal. There is no measure-identification premise. -/
theorem shape_expectation (N : ℕ) (f : ℕ → ℝ) :
    (∑ s : Fin (N + 1), shapeProbability N s * f s) = expectation N f := by
  classical
  unfold shapeProbability expectation
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  let s : Fin (N + 1) := ⟨spin N p, Nat.lt_succ_of_le (spin_le_length N p)⟩
  rw [Finset.sum_eq_single s]
  · simp [s]
  · intro b hb hbs
    have hneq : spin N p ≠ b.val := by
      intro heq
      apply hbs
      exact Fin.ext heq.symm
    simp [hneq]
  · simp

theorem shapeProbability_sum (N : ℕ) :
    (∑ s : Fin (N + 1), shapeProbability N s) = 1 := by
  have h := (shape_expectation N (fun _ => 1)).trans (expectation_one N)
  simpa only [mul_one] using h

/-- The exact rank-two combinatorial dimension count, in natural numbers. -/
theorem dimension_count_identity (N : ℕ) :
    (∑ s : Fin (N + 1), (s.val + 1) * tableauPathCount N s) = 2 ^ N := by
  have h : (∑ s : Fin (N + 1), ((s.val : ℝ) + 1) * tableauPathCount N s) /
      (2 : ℝ) ^ N = 1 := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    simpa only [shapeProbability_formula, div_eq_mul_inv] using shapeProbability_sum N
  have hden : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq := (div_eq_one_iff_eq hden).mp h
  exact_mod_cast heq

theorem shape_spinCasimir_moment (N : ℕ) :
    (∑ s : Fin (N + 1), shapeProbability N s * spinCasimir s) = 3 * (N : ℝ) :=
  (shape_expectation N spinCasimir).trans (expectation_spinCasimir N)

theorem upperRow_eq_of_legal (N : ℕ) (p : Path N) (hp : legal N p) :
    upperRow N p = (N + spin N p) / 2 := by
  have := row_sum N p
  have := spin_add_lower_eq_upper N p hp
  omega

theorem lowerRow_eq_of_legal (N : ℕ) (p : Path N) (hp : legal N p) :
    lowerRow N p = (N - spin N p) / 2 := by
  have := row_sum N p
  have := spin_add_lower_eq_upper N p hp
  omega

/-- The centered variance of the two integer row lengths of a shape. -/
def shapeVariance (N s : ℕ) : ℝ :=
  (((N + s) / 2 : ℕ) - (N : ℝ) / 2) ^ 2 +
    (((N - s) / 2 : ℕ) - (N : ℝ) / 2) ^ 2

/-- The concrete shape law obeys the manuscript's second-moment estimate. -/
theorem shape_centered_second_moment_le (N : ℕ) :
    (∑ s : Fin (N + 1), shapeProbability N s * shapeVariance N s) ≤
      3 * (N : ℝ) / 2 := by
  rw [shape_expectation]
  have heq : expectation N (shapeVariance N) =
      ∑ p : Path N, weight N p * rowVariance N p := by
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hl : legal N p
    · simp only [shapeVariance, rowVariance, upperRow_eq_of_legal N p hl,
        lowerRow_eq_of_legal N p hl]
    · rw [weight_eq_zero_of_not_legal N p hl]
      simp
  rw [heq]
  exact centered_second_moment_le N

end Cloning.YoungTwoRow
