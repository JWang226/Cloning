import Cloning.BosonicNumberLaw
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Stochastic domination of seeded bosonic number laws

The hockey-stick binomial identity gives the exact convolution of a seeded
number law with one further geometric variable. Nonnegative decreasing tests
then have decreasing expectations with the seed. Such tests are automatically
bounded by their value at zero, which also proves all required summability.
-/

noncomputable section
open scoped BigOperators Topology
namespace Cloning.BosonicStochasticOrder

open Cloning BosonicNumberLaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- One more seed quantum adds an independent geometric number variable.
This is an exact finite coefficient identity, not a distribution hypothesis. -/
theorem seededLaw_succ_convolution (r : ℝ) (l k : ℕ) :
    seededLaw r (l + 1) k =
      ∑ t ∈ Finset.range (k + 1), seededLaw r l t * Thermal.geometric r (k - t) := by
  have hterm (t : ℕ) (ht : t ∈ Finset.range (k + 1)) :
      seededLaw r l t * Thermal.geometric r (k - t) =
        ((t + l).choose l : ℝ) * ((1 - r) ^ (l + 1 + 1) * r ^ k) := by
    have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hp : r ^ t * r ^ (k - t) = r ^ k := by
      rw [← pow_add, Nat.add_sub_of_le htk]
    unfold seededLaw Thermal.geometric
    rw [Nat.add_comm l t, pow_succ (1 - r) (l + 1)]
    calc
      _ = ((t + l).choose l : ℝ) * ((1 - r) ^ (l + 1) * (1 - r)) *
          (r ^ t * r ^ (k - t)) := by ring
      _ = _ := by rw [hp]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum,
    Nat.sum_range_add_choose]
  unfold seededLaw
  rw [show l + 1 + k = k + l + 1 by omega]
  ring

/-- Decreasing nonnegative tests are summable against every seeded law. -/
theorem seededLaw_weighted_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℕ → ℝ} (hw0 : ∀ k, 0 ≤ w k) (hw : Antitone w) (l : ℕ) :
    Summable (fun k ↦ seededLaw r l k * w k) := by
  apply ((seededLaw_hasSum hr0 hr1 l).summable.mul_right (w 0)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (seededLaw_nonneg hr0 hr1 l k) (hw0 k))]
  exact mul_le_mul_of_nonneg_left (hw (Nat.zero_le k)) (seededLaw_nonneg hr0 hr1 l k)

/-- Adding a geometric summand decreases the expectation of every decreasing
nonnegative test, with all infinite sums justified by absolute convergence. -/
theorem seededLaw_succ_antitone_moment_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℕ → ℝ} (hw0 : ∀ k, 0 ≤ w k) (hw : Antitone w) (l : ℕ) :
    (∑' k, seededLaw r (l + 1) k * w k) ≤ ∑' k, seededLaw r l k * w k := by
  have hs := seededLaw_weighted_summable hr0 hr1 hw0 hw l
  have hg := Thermal.geometric_hasSum hr0 hr1
  have hsN : Summable (fun k ↦ ‖seededLaw r l k * w k‖) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (seededLaw_nonneg hr0 hr1 l _) (hw0 _))] using hs
  have hgN : Summable (fun k ↦ ‖Thermal.geometric r k‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Thermal.geometric_nonneg hr0 hr1.le _)]
      using hg.summable
  have hc := hasSum_sum_range_mul_of_summable_norm hsN hgN
  calc
    _ ≤ ∑' k, ∑ t ∈ Finset.range (k + 1),
        (seededLaw r l t * w t) * Thermal.geometric r (k - t) := by
      apply (seededLaw_weighted_summable hr0 hr1 hw0 hw (l + 1)).tsum_le_tsum _ hc.summable
      intro k
      rw [seededLaw_succ_convolution, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro t ht
      have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      calc
        seededLaw r l t * Thermal.geometric r (k - t) * w k ≤
            seededLaw r l t * Thermal.geometric r (k - t) * w t :=
          mul_le_mul_of_nonneg_left (hw htk)
            (mul_nonneg (seededLaw_nonneg hr0 hr1 l t) (Thermal.geometric_nonneg hr0 hr1.le _))
        _ = _ := by ring
    _ = _ := by rw [hc.tsum_eq, hg.tsum_eq, mul_one]

/-- Full one-mode least-noise moment bound for every bounded nonnegative
nonincreasing test. Boundedness follows from nonincreasingness on `ℕ`. -/
theorem seededLaw_antitone_moment_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℕ → ℝ} (hw0 : ∀ k, 0 ≤ w k) (hw : Antitone w) (l : ℕ) :
    (∑' k, seededLaw r l k * w k) ≤ ∑' k, Thermal.geometric r k * w k := by
  induction l with
  | zero => simp only [seededLaw_zero, le_refl]
  | succ l ih => exact (seededLaw_succ_antitone_moment_le hr0 hr1 hw0 hw l).trans ih

end Cloning.BosonicStochasticOrder
