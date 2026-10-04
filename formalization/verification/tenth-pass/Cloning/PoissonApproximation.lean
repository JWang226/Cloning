import Cloning.CountableScheffe
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial-to-Poisson convergence of coherent-product number coefficients

This is the concrete probability calculation in `coherent-product-limit`.
Both laws are defined explicitly; positivity, exact normalization, pointwise
convergence, full `ℓ¹` convergence, and square-root amplitude convergence are
proved. No probability normalization or convergence is assumed.

The occupation basis, the quantum embedding, and the identification of these
coefficients with coherent/product vectors remain separate constructions.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace Cloning.PoissonApproximation

/-- The number distribution of the length-`L` coherent-product approximation.
Natural binomial coefficients automatically pad this distribution by zero
beyond occupation `L`. The convention at `L = 0` is the vacuum law. -/
def binomialWeight (t : ℝ) (L j : ℕ) : ℝ :=
  (L.choose j : ℝ) * (t / L) ^ j / (1 + t / L) ^ L

/-- The Poisson number distribution of a coherent vector with squared
amplitude `t`. -/
def poissonWeight (t : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-t) * t ^ j / j.factorial

theorem binomialWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (L j : ℕ) :
    0 ≤ binomialWeight t L j := by
  unfold binomialWeight
  positivity

theorem poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    0 ≤ poissonWeight t j := by
  unfold poissonWeight
  positivity

theorem binomialWeight_eq_zero_of_lt (t : ℝ) {L j : ℕ} (hLj : L < j) :
    binomialWeight t L j = 0 := by
  simp [binomialWeight, Nat.choose_eq_zero_of_lt hLj]

/-- Exact normalization, including the zero-length and zero-amplitude cases. -/
theorem binomialWeight_sum {t : ℝ} (ht : 0 ≤ t) (L : ℕ) :
    ∑ j ∈ Finset.range (L + 1), binomialWeight t L j = 1 := by
  have hden : (1 + t / L : ℝ) ^ L ≠ 0 := by positivity
  have hbin : (∑ j ∈ Finset.range (L + 1), (L.choose j : ℝ) * (t / L) ^ j) =
      (1 + t / L) ^ L := by
    simpa only [one_pow, mul_one, mul_comm, add_comm] using
      (add_pow (t / L) (1 : ℝ) L).symm
  simp only [binomialWeight, ← Finset.sum_div, hbin, div_self hden]

theorem binomialWeight_hasSum {t : ℝ} (ht : 0 ≤ t) (L : ℕ) :
    HasSum (binomialWeight t L) 1 := by
  rw [← binomialWeight_sum ht L]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  exact binomialWeight_eq_zero_of_lt t
    (by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hj)

theorem poissonWeight_hasSum {t : ℝ} (ht : 0 ≤ t) :
    HasSum (poissonWeight t) 1 := by
  exact ProbabilityTheory.poissonPMFRealSum ⟨t, ht⟩

/-- The scaled binomial coefficient converges to the corresponding exponential
series coefficient. -/
theorem tendsto_binomial_numerator (t : ℝ) (j : ℕ) :
    Tendsto (fun L : ℕ => (L.choose j : ℝ) * (t / L) ^ j) atTop
      (𝓝 (t ^ j / j.factorial)) := by
  apply ProbabilityTheory.tendsto_choose_mul_pow_atTop
  change Tendsto (fun L : ℕ => (L : ℝ) * (t / L)) atTop (𝓝 t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  field_simp

/-- The actual binomial probabilities converge pointwise to the Poisson law. -/
theorem binomialWeight_tendsto (t : ℝ) (j : ℕ) :
    Tendsto (fun L => binomialWeight t L j) atTop (𝓝 (poissonWeight t j)) := by
  have h := (tendsto_binomial_numerator t j).div (Real.tendsto_one_add_div_pow_exp t)
    (Real.exp_ne_zero t)
  change Tendsto (fun L => binomialWeight t L j) atTop
    (𝓝 (t ^ j / j.factorial / Real.exp t)) at h
  have he : t ^ j / j.factorial / Real.exp t = poissonWeight t j := by
    unfold poissonWeight
    rw [Real.exp_neg]
    ring
  rwa [he] at h

/-- Full `ℓ¹` convergence of the concrete number distributions. -/
theorem binomialWeight_l1_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun L => CountableScheffe.l1Distance (binomialWeight t L) (poissonWeight t))
      atTop (𝓝 0) :=
  CountableScheffe.discrete_scheffe _ _
    (binomialWeight_nonneg ht) (poissonWeight_nonneg ht)
    (binomialWeight_hasSum ht) (poissonWeight_hasSum ht) (binomialWeight_tendsto t)

/-- Square-root amplitude convergence in the coherent-product calculation. -/
theorem sqrt_binomialWeight_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun L => ∑' j, (Real.sqrt (binomialWeight t L j) -
      Real.sqrt (poissonWeight t j)) ^ 2) atTop (𝓝 0) :=
  CountableScheffe.sqrt_amplitudes_tendsto_of_pointwise _ _
    (binomialWeight_nonneg ht) (poissonWeight_nonneg ht)
    (binomialWeight_hasSum ht) (poissonWeight_hasSum ht) (binomialWeight_tendsto t)

end Cloning.PoissonApproximation
