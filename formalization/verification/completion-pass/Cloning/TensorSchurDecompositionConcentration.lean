import Cloning.TensorSchurDecompositionBounds
import Cloning.YoungGeneralPMF

/-! Concentration of the actual physical Young-label PMF, uniformly over the
ordered probability simplex. No tableau-character identification is required. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

def physicalStandardWordWeight (p : Fin d → ℝ) (w : Fin n → Fin d) : ℝ :=
  if IsStandardWord w then physicalSectorCharacter (rowCount w) p else 0

theorem physicalStandardWordWeight_nonneg (p : Fin d → ℝ) (w : Fin n → Fin d) :
    0 ≤ physicalStandardWordWeight p w := by
  unfold physicalStandardWordWeight
  split_ifs
  · exact physicalSectorCharacter_nonneg _ _
  · exact le_rfl

theorem physicalStandardWordWeight_le (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (horder : Antitone p) (w : Fin n → Fin d) :
    physicalStandardWordWeight p w ≤
      ((n * d + 1 : ℕ) : ℝ) ^ Fintype.card (PositiveRoot d) * wordWeight p w := by
  unfold physicalStandardWordWeight
  split_ifs
  · rw [wordWeight_eq_row_product]
    simpa only [sum_rowCount] using
      physicalSectorCharacter_le_polynomial_highest (rowCount w) p hp horder
  · exact mul_nonneg (by positivity) (wordWeight_nonneg p hp w)

theorem sum_physicalStandardWordWeight_shape (p : Fin d → ℝ) (mu : Fin d → ℕ) :
    (∑ w : Fin n → Fin d, if rowCount w = mu then physicalStandardWordWeight p w else 0) =
      (standardCount n mu : ℝ) * physicalSectorCharacter mu p := by
  have hpoint (w : Fin n → Fin d) :
      (if rowCount w = mu then physicalStandardWordWeight p w else 0) =
        if IsStandardWord w ∧ rowCount w = mu then physicalSectorCharacter mu p else 0 := by
    unfold physicalStandardWordWeight
    split_ifs <;> simp_all
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [standardCount]

theorem tensorYoungPMF_sum_mul (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (f : Shape d n → ℝ) :
    (∑ mu : Shape d n, (tensorYoungPMF n d p hp hs mu).toReal * f mu) =
      ∑ w : Fin n → Fin d, physicalStandardWordWeight p w * f (wordShape w) := by
  simp_rw [tensorYoungPMF_formula, ← sum_physicalStandardWordWeight_shape]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [← wordShape_eq_iff, ite_mul, zero_mul]
  simp

theorem tensorYoungPMF_tail_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (ε : ℝ) :
    0 ≤ tailProbability (tensorYoungPMF n d p hp hs) p ε := by
  apply Finset.sum_nonneg
  intro mu _
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- The actual Schur measurement law has an explicit polynomial times
exponential deviation bound, including repeated and zero eigenvalues. -/
theorem tensorYoungPMF_tail_le (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (horder : Antitone p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε2 : ε ≤ 2) :
    tailProbability (tensorYoungPMF n d p hp hs) p ε ≤
      ((n * d + 1 : ℕ) : ℝ) ^ Fintype.card (PositiveRoot d) *
        (2 * d * Real.exp (-(n : ℝ) * ε ^ 2 / 4)) := by
  have he := tensorYoungPMF_sum_mul (n := n) p hp hs (fun mu =>
    if ∃ i, (n : ℝ) * ε ≤ |((mu i).val : ℝ) - n * p i| then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, wordShape_val] at he
  change (∑ mu : Shape d n,
    if ∃ i, (n : ℝ) * ε ≤ |((mu i).val : ℝ) - n * p i| then
      (tensorYoungPMF n d p hp hs mu).toReal else 0) ≤ _
  rw [he]
  calc
    _ ≤ ∑ w : Fin n → Fin d,
        ((n*d+1 : ℕ) : ℝ)^Fintype.card (PositiveRoot d) *
          (if ∃ i, (n : ℝ)*ε ≤ |(rowCount w i : ℝ)-n*p i| then wordWeight p w else 0) := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact physicalStandardWordWeight_le p hp horder w
      · simp
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_rowCount_tail_le p hp hs ε hε hε2) (by positivity)

/-- Comparison with an already proved vanishing stretched-exponential envelope. -/
theorem tensorYoungPMF_tail_shrinking_le (n : ℕ) (hn : 1 ≤ n)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (horder : Antitone p) :
    tailProbability (tensorYoungPMF n d p hp hs) p (shrinkingRadius n) ≤
      ((d : ℝ)+1)^Fintype.card (PositiveRoot d) *
        (((n : ℝ)+1)^Fintype.card (PositiveRoot d) * concentrationEnvelope d n) := by
  have ht := tensorYoungPMF_tail_le (n := n) p hp hs horder (shrinkingRadius n)
    (shrinkingRadius_nonneg n) ((shrinkingRadius_le_one n hn).trans (by norm_num))
  have he : -(n : ℝ) * shrinkingRadius n ^ 2 / 4 = -((n : ℝ)^(1/3 : ℝ))/4 := by
    rw [neg_mul, sample_mul_radius_sq n (by omega)]
  rw [he] at ht
  apply ht.trans
  let s := Fintype.card (PositiveRoot d)
  have hpoly : ((n*d+1 : ℕ) : ℝ)^s ≤ ((d:ℝ)+1)^s * ((n:ℝ)+1)^s := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hone : (1:ℝ) ≤ ((n:ℝ)+1)^(d*d) := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hmul := mul_le_mul_of_nonneg_right hpoly
    (show 0 ≤ 2*d*Real.exp (-((n:ℝ)^(1/3:ℝ))/4) by positivity)
  have hfinal := mul_le_mul_of_nonneg_left hone
    (show 0 ≤ (((d:ℝ)+1)^s * ((n:ℝ)+1)^s) *
      (2*d*Real.exp (-((n:ℝ)^(1/3:ℝ))/4)) by positivity)
  dsimp only [concentrationEnvelope]
  dsimp only [s] at hmul hfinal
  nlinarith

/-- Physical Young labels concentrate uniformly for every moving ordered
spectrum in the closed probability simplex. -/
theorem tensorYoungPMF_tail_tendsto_zero (p : ℕ → Fin d → ℝ)
    (hp : ∀ n a, 0 ≤ p n a) (hs : ∀ n, ∑ a, p n a = 1)
    (horder : ∀ n, Antitone (p n)) :
    Tendsto (fun n => tailProbability (tensorYoungPMF n d (p n) (hp n) (hs n))
      (p n) (shrinkingRadius n)) atTop (𝓝 0) := by
  have ht := (polynomial_concentrationEnvelope_tendsto_zero d
    (Fintype.card (PositiveRoot d))).const_mul (((d:ℝ)+1)^Fintype.card (PositiveRoot d))
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => tensorYoungPMF_tail_nonneg _ _ _ _)) ?_ ht
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact tensorYoungPMF_tail_shrinking_le n hn (p n) (hp n) (hs n) (horder n)

end Cloning.TensorLie
