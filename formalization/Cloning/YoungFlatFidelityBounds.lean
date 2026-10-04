import Cloning.ClassicalFidelity
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Scalar square-root product estimates valid for every finite coupling. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory Filter
namespace Cloning.YoungFlat
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]

theorem weighted_sqrt_le (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, p i*Real.sqrt (f i)) ≤ Real.sqrt (∑ i, p i*f i) := by
  have hh := Real.sum_sqrt_mul_sqrt_le Finset.univ hp (fun i ↦ mul_nonneg (hp i) (hf i))
  have he i : Real.sqrt (p i)*Real.sqrt (p i*f i)=p i*Real.sqrt (f i) := by
    rw [Real.sqrt_mul (hp i), ← mul_assoc, Real.mul_self_sqrt (hp i)]
  simpa only [he, hs, Real.sqrt_one, one_mul] using hh

theorem weighted_sqrt_product_error (p A B : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (C : ℝ) (hAC : ∀ i, A i ≤ C) :
    (∑ i, p i*|Real.sqrt (A i*B i)-1|) ≤
      Real.sqrt (C*(∑ i, p i*|B i-1|)+(∑ i, p i*|A i-1|)) := by
  have hpoint i : |A i*B i-1| ≤ C*|B i-1|+|A i-1| := by
    calc
      _ = |A i*(B i-1)+(A i-1)| := by congr 1; ring
      _ ≤ |A i*(B i-1)|+|A i-1| := abs_add_le _ _
      _ = A i*|B i-1|+|A i-1| := by rw [abs_mul, abs_of_nonneg (hA i)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hAC i) (abs_nonneg _)) le_rfl
  calc
    _ ≤ ∑ i, p i*Real.sqrt |A i*B i-1| := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp i)
      simpa only [Real.sqrt_one] using Cloning.ClassicalFidelity.sqrt_difference_bound
        (A i*B i) 1 (mul_nonneg (hA i) (hB i)) zero_le_one
    _ ≤ Real.sqrt (∑ i, p i*|A i*B i-1|) :=
      weighted_sqrt_le p _ hp hs (fun _ ↦ abs_nonneg _)
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      calc
        _ ≤ ∑ i, p i*(C*|B i-1|+|A i-1|) :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hpoint i) (hp i)
        _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- Deleting any bad set costs its probability mass times the reference scalar. -/
theorem weighted_truncated_sqrt_error (p A B : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (C : ℝ) (hAC : ∀ i, A i ≤ C) (q : ℝ) (hq : 0 ≤ q) (good : ι → Prop) :
    |(∑ i, p i*(if good i then q*Real.sqrt (A i*B i) else 0))-q| ≤
      q*(Real.sqrt (C*(∑ i, p i*|B i-1|)+(∑ i, p i*|A i-1|))+
        ∑ i, if good i then 0 else p i) := by
  have he : (∑ i, p i*(if good i then q*Real.sqrt (A i*B i) else 0))-q =
      ∑ i, p i*((if good i then q*Real.sqrt (A i*B i) else 0)-q) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  rw [he]
  calc
    _ ≤ ∑ i, |p i*((if good i then q*Real.sqrt (A i*B i) else 0)-q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (p i*(q*|Real.sqrt (A i*B i)-1|)+(if good i then 0 else q*p i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hp i)]
      by_cases hi : good i
      · simp only [if_pos hi, add_zero]
        have heq : q*Real.sqrt (A i*B i)-q=q*(Real.sqrt (A i*B i)-1) := by ring
        rw [heq, abs_mul, abs_of_nonneg hq]
      · simp only [if_neg hi, zero_sub, abs_neg, abs_of_nonneg hq]
        nlinarith [mul_nonneg (hp i) (mul_nonneg hq (abs_nonneg (Real.sqrt (A i*B i)-1)))]
    _ = q*(∑ i, p i*|Real.sqrt (A i*B i)-1|)+q*(∑ i, if good i then 0 else p i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl; intro i _; ring
      · apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
    _ ≤ _ := by
      nlinarith [weighted_sqrt_product_error p A B hp hs hA hB C hAC]

/-- The finite PMF change-of-variables formula in real weights. -/
theorem pmf_sum_map {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (f : α → β) (g : β → ℝ) :
    (∑ a, (P a).toReal*g (f a)) = ∑ b, (P.map f b).toReal*g b := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  have hf : Measurable f := measurable_of_countable f
  have hg : AEStronglyMeasurable g ((P.map f).toMeasure) :=
    (measurable_of_countable g).aestronglyMeasurable
  rw [← PMF.toMeasure_map f P hf] at hg
  have he := integral_map hf.aemeasurable hg
  rw [PMF.toMeasure_map f P hf] at he
  simpa only [PMF.integral_eq_sum, smul_eq_mul] using he.symm

end Cloning.YoungFlat
