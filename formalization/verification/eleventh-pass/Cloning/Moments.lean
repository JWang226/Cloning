import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The order and moment steps of the Gaussian converse

This file proves the stochastic-coupling implication in
`prop:least-noise-moment`, a finite diagonal version of the weighted fidelity
bound, and the last limit argument of `prop:flat-prior-converse`.
It does NOT construct the bosonic amplifier, identify its number distribution,
or prove the compact-CP-map subsequence theorem. In particular, the coupling
theorem is applicable to arbitrarily correlated idlers: no independence
assumption is used once a coupling with coordinatewise domination is given.
-/

open scoped BigOperators
open Filter MeasureTheory

namespace Cloning.Moments

/-- A nonnegative antitone product decreases under coordinatewise domination. -/
theorem antitone_product_le {ι : Type*} [Fintype ι]
    (w : ι → ℕ → ℝ) (hw : ∀ i n, 0 ≤ w i n)
    (hanti : ∀ i, Antitone (w i)) (x y : ι → ℕ)
    (hxy : ∀ i, x i ≤ y i) :
    (∏ i, w i (y i)) ≤ ∏ i, w i (x i) := by
  exact Finset.prod_le_prod (fun i _ => hw i (y i))
    (fun i _ => hanti i (hxy i))

/-- Adding any number of nonnegative occupation counts dominates the first count. -/
theorem first_count_le_sum (x : ℕ → ℕ) (l : ℕ) :
    x 0 ≤ ∑ j ∈ Finset.range (l + 1), x j := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.zero_lt_succ l))

/-- The pathwise part of the negative-binomial coupling used in the manuscript. -/
theorem occupation_product_le {ι : Type*} [Fintype ι]
    (w : ι → ℕ → ℝ) (hw : ∀ i n, 0 ≤ w i n)
    (hanti : ∀ i, Antitone (w i)) (x : ι → ℕ → ℕ) (l : ι → ℕ) :
    (∏ i, w i (∑ j ∈ Finset.range (l i + 1), x i j)) ≤
      ∏ i, w i (x i 0) := by
  exact antitone_product_le w hw hanti (fun i => x i 0)
    (fun i => ∑ j ∈ Finset.range (l i + 1), x i j)
    (fun i => first_count_le_sum (x i) (l i))

/-- An actual Bochner-integral moment inequality, on an arbitrary probability
space (indeed an arbitrary measure). Integrability is explicit. -/
theorem coupled_moment_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : ι → ℕ → ℝ)
    (hw : ∀ i n, 0 ≤ w i n) (hanti : ∀ i, Antitone (w i))
    (x y : Ω → ι → ℕ) (hxy : ∀ᵐ ω ∂μ, ∀ i, x ω i ≤ y ω i)
    (hx : Integrable (fun ω => ∏ i, w i (x ω i)) μ)
    (hy : Integrable (fun ω => ∏ i, w i (y ω i)) μ) :
    (∫ ω, ∏ i, w i (y ω i) ∂μ) ≤ ∫ ω, ∏ i, w i (x ω i) ∂μ := by
  apply integral_mono_ae hy hx
  filter_upwards [hxy] with ω hω
  exact antitone_product_le w hw hanti (x ω) (y ω) hω

/-- Correlated random idler occupations require no product assumption. -/
theorem random_idler_moment_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : ι → ℕ → ℝ)
    (hw : ∀ i n, 0 ≤ w i n) (hanti : ∀ i, Antitone (w i))
    (x : Ω → ι → ℕ → ℕ) (l : Ω → ι → ℕ)
    (hx : Integrable (fun ω => ∏ i, w i (x ω i 0)) μ)
    (hy : Integrable
      (fun ω => ∏ i, w i (∑ j ∈ Finset.range (l ω i + 1), x ω i j)) μ) :
    (∫ ω, ∏ i, w i (∑ j ∈ Finset.range (l ω i + 1), x ω i j) ∂μ) ≤
      ∫ ω, ∏ i, w i (x ω i 0) ∂μ := by
  exact integral_mono hy hx (fun ω => occupation_product_le w hw hanti (x ω) (l ω))

/-- Classical/diagonal weighted root-fidelity bound, with no normalization
assumption. This is not the noncommutative trace-class version. -/
theorem weighted_affinity_sq_le {ι : Type*} [Fintype ι]
    (r t w : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hw : ∀ i, 0 < w i) :
    (∑ i, Real.sqrt (r i * t i)) ^ 2 ≤
      (∑ i, r i * w i) * ∑ i, t i / w i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro i _
    exact mul_nonneg (hr i) (hw i).le
  · intro i _
    exact div_nonneg (ht i) (hw i).le
  · intro i _
    rw [Real.sq_sqrt (mul_nonneg (hr i) (ht i))]
    field_simp [ne_of_gt (hw i)]

/-- Fidelity-from-moment conclusion, retaining the possibly deficient trace.
The weighted inequality and least-noise moment are premises, not axioms. -/
theorem fidelity_le_of_moment {f m c o t : ℝ}
    (hc : 0 ≤ c) (ho : 0 ≤ o) (htrace : t ≤ c)
    (hmoment : m ≤ t * o) (hweighted : f ^ 2 ≤ m * c * o) :
    f ≤ c * o := by
  have hmo : m ≤ c * o := hmoment.trans (mul_le_mul_of_nonneg_right htrace ho)
  have hco : 0 ≤ c * o := mul_nonneg hc ho
  have hsq : f ^ 2 ≤ (c * o) ^ 2 := by
    calc
      f ^ 2 ≤ m * c * o := hweighted
      _ = m * (c * o) := by ring
      _ ≤ (c * o) * (c * o) := mul_le_mul_of_nonneg_right hmo hco
      _ = (c * o) ^ 2 := by ring
  nlinarith [sq_nonneg (f - c * o)]

/-- Last subsequence argument of the flat-prior converse. The analytic task of
constructing convergent moment subsequences is explicitly outside this lemma. -/
theorem flat_prior_limit_bound {f m : ℕ → ℝ} {F M c o t : ℝ}
    (hf : Tendsto f atTop (nhds F)) (hm : Tendsto m atTop (nhds M))
    (hc : 0 ≤ c) (ho : 0 ≤ o) (htrace : t ≤ c)
    (hmoment : M ≤ t * o)
    (hweighted : ∀ᶠ n in atTop, f n ^ 2 ≤ m n * c * o) : F ≤ c * o := by
  have hlimit : F ^ 2 ≤ M * c * o :=
    le_of_tendsto_of_tendsto (hf.pow 2) ((hm.mul_const c).mul_const o) hweighted
  exact fidelity_le_of_moment hc ho htrace hmoment hlimit

end Cloning.Moments
