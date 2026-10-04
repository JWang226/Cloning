import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The finite block-weight argument in cloning.tex

This file proves the classical and scalar analytic part of Lemma
`lifted-fidelity-factorization`. `classicalAffinity` is the unsquared classical
fidelity. The final bound has precisely the paper's `η + 2 * √ε` constant.

The exact finite-matrix direct-sum identity is proved separately in
`Cloning.MatrixFidelityLifted`, and the positive-deletion estimate is proved in
`Cloning.MatrixFidelityDeletion`. Both are instantiated in the concrete version
`Cloning.MatrixFidelityAsymptotics`. This scalar module retains explicit
interfaces; the uniform sector-mixture estimate remains an asymptotic input.
This file alone does not establish the paper's asymptotic cloning theorem.
-/

noncomputable section
open scoped BigOperators
namespace Cloning.BlockFidelity

variable {ι : Type*} [Fintype ι]

/-- Unsquared classical fidelity, also called the Hellinger affinity. -/
def classicalAffinity (p q : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i) * Real.sqrt (q i)

lemma classicalAffinity_nonneg (p q : ι → ℝ) :
    0 ≤ classicalAffinity p q := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma classicalAffinity_comm (p q : ι → ℝ) :
    classicalAffinity p q = classicalAffinity q p := by
  simp only [classicalAffinity, mul_comm]

lemma classicalAffinity_self (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    classicalAffinity p p = ∑ i, p i := by
  simp only [classicalAffinity, Real.mul_self_sqrt (hp _)]

lemma classicalAffinity_le_one (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i ≤ 1) (hqs : ∑ i, q i ≤ 1) :
    classicalAffinity p q ≤ 1 := by
  have hCS := Real.sum_sqrt_mul_sqrt_le Finset.univ hp hq
  calc
    classicalAffinity p q ≤ Real.sqrt (∑ i, p i) * Real.sqrt (∑ i, q i) := hCS
    _ ≤ 1 * 1 := mul_le_mul (Real.sqrt_le_one.mpr hps)
      (Real.sqrt_le_one.mpr hqs) (Real.sqrt_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The scalar square-root estimate needed when a nonnegative block is removed. -/
lemma sqrt_sub_sqrt_le_sqrt_sub {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    Real.sqrt x - Real.sqrt y ≤ Real.sqrt (x - y) := by
  have hx : 0 ≤ x := le_trans hy hyx
  have hd : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hx2 := Real.sq_sqrt hx
  have hy2 := Real.sq_sqrt hy
  have hd2 := Real.sq_sqrt hd
  have hprod := mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg (x-y))
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  have hsd := Real.sqrt_nonneg (x-y)
  nlinarith

lemma classicalAffinity_mono_left (q qG p : ι → ℝ)
    (hle : ∀ i, qG i ≤ q i) :
    classicalAffinity qG p ≤ classicalAffinity q p := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (hle i)) (Real.sqrt_nonneg _)

/-- Removing total mass ε changes classical fidelity by at most √ε. -/
lemma classicalAffinity_trim_bound (q qG p : ι → ℝ)
    (hqG : ∀ i, 0 ≤ qG i) (hp : ∀ i, 0 ≤ p i)
    (hle : ∀ i, qG i ≤ q i) (hps : ∑ i, p i = 1) :
    |classicalAffinity q p - classicalAffinity qG p| ≤
      Real.sqrt (∑ i, (q i - qG i)) := by
  have hdiff : ∀ i, 0 ≤ q i - qG i := fun i => sub_nonneg.mpr (hle i)
  rw [abs_of_nonneg (sub_nonneg.mpr (classicalAffinity_mono_left q qG p hle))]
  calc
    classicalAffinity q p - classicalAffinity qG p =
        ∑ i, (Real.sqrt (q i) - Real.sqrt (qG i)) * Real.sqrt (p i) := by
      simp [classicalAffinity, Finset.sum_sub_distrib, sub_mul]
    _ ≤ ∑ i, Real.sqrt (q i - qG i) * Real.sqrt (p i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (sqrt_sub_sqrt_le_sqrt_sub (hqG i) (hle i)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (∑ i, (q i - qG i)) * Real.sqrt (∑ i, p i) := by
      simpa using Real.sum_sqrt_mul_sqrt_le Finset.univ hdiff hp
    _ = Real.sqrt (∑ i, (q i - qG i)) := by rw [hps, Real.sqrt_one, mul_one]

/-- A uniform estimate on the normalized sector fidelities passes through the
classical block weights without increasing its error. -/
lemma weighted_sector_error (p q f : ι → ℝ) (c η : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i ≤ 1) (hqs : ∑ i, q i ≤ 1)
    (hη : 0 ≤ η) (herr : ∀ i, 0 < q i → |f i - c| ≤ η) :
    |(∑ i, Real.sqrt (q i) * Real.sqrt (p i) * f i) -
      c * classicalAffinity q p| ≤ η := by
  have hw : ∀ i, 0 ≤ Real.sqrt (q i) * Real.sqrt (p i) :=
    fun i => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    |(∑ i, Real.sqrt (q i) * Real.sqrt (p i) * f i) -
        c * classicalAffinity q p| =
        |∑ i, (Real.sqrt (q i) * Real.sqrt (p i)) * (f i - c)| := by
      congr 1
      rw [classicalAffinity, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |(Real.sqrt (q i) * Real.sqrt (p i)) * (f i - c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (Real.sqrt (q i) * Real.sqrt (p i)) * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      by_cases hpos : 0 < q i
      · exact mul_le_mul_of_nonneg_left (herr i hpos) (hw i)
      · have hz : q i = 0 := le_antisymm (le_of_not_gt hpos) (hq i)
        simp [hz]
    _ = classicalAffinity q p * η := by simp [classicalAffinity, Finset.sum_mul]
    _ ≤ 1 * η := mul_le_mul_of_nonneg_right
      (classicalAffinity_le_one q p hq hp hqs hps) hη
    _ = η := one_mul _

/-- The finite quantitative estimate behind the lifted fidelity factorization.

`actual` denotes the full quantum fidelity, while `f` lists normalized retained
sector fidelities. `hquantum` is exactly the consequence of quantum fidelity
continuity after deleting positive blocks of the indicated total mass. The
remaining classical continuity and summation steps are proved in this file. -/
lemma lifted_factorization_bound (p q qG f : ι → ℝ) (actual c η : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hqG : ∀ i, 0 ≤ qG i)
    (hle : ∀ i, qG i ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ i, 0 < qG i → |f i - c| ≤ η)
    (hquantum : |actual - ∑ i, Real.sqrt (qG i) * Real.sqrt (p i) * f i| ≤
      Real.sqrt (∑ i, (q i - qG i))) :
    |actual - c * classicalAffinity q p| ≤
      η + 2 * Real.sqrt (∑ i, (q i - qG i)) := by
  have hqGs : ∑ i, qG i ≤ 1 := (Finset.sum_le_sum fun i _ => hle i).trans hqs
  have hretained := weighted_sector_error p qG f c η hp hqG
    (le_of_eq hps) hqGs hη hsector
  have hlabel := classicalAffinity_trim_bound q qG p hqG hp hle hps
  have hlabel' : |c * classicalAffinity qG p - c * classicalAffinity q p| ≤
      Real.sqrt (∑ i, (q i - qG i)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hlabel hc0).trans
      (by simpa using (mul_le_mul_of_nonneg_right hc1
        (Real.sqrt_nonneg (∑ i, (q i - qG i)))))
  have htriangle := abs_sub_le actual
    (∑ i, Real.sqrt (qG i) * Real.sqrt (p i) * f i)
    (c * classicalAffinity qG p)
  have htriangle' := abs_sub_le actual (c * classicalAffinity qG p)
    (c * classicalAffinity q p)
  linarith

end Cloning.BlockFidelity
