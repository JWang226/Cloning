import Cloning.ClassicalFidelity
import Cloning.Thermal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Discrete Scheffé and countable Hellinger convergence

This proves the pointwise-to-`ℓ¹` upgrade invoked in the Werner occupation
and coherent-product arguments of `cloning.tex`, using the overlap `min(pₙ,p)`
and Tannery's theorem. No `ℓ¹` limit or uniform domination of the original
laws is assumed. The index type may be any type, in particular a countable
Fock occupation lattice.

The pinned Mathlib input is `tendsto_tsum_of_dominated_convergence` in
`Mathlib.Analysis.Normed.Group.Tannery`. The actual Werner binomial-ratio
pointwise limit and its quantum occupation-space identification remain
separate obligations.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.CountableScheffe

variable {ι : Type*}

def l1Distance (p q : ι → ℝ) : ℝ := ∑' i, |p i - q i|

def affinity (p q : ι → ℝ) : ℝ := ∑' i, Real.sqrt (p i) * Real.sqrt (q i)

theorem affinity_comm (p q : ι → ℝ) : affinity p q = affinity q p := by
  unfold affinity
  apply tsum_congr
  intro i
  exact mul_comm _ _

theorem summable_min (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsq : Summable q) : Summable (fun i ↦ min (p i) (q i)) := by
  apply hsq.of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp i) (hq i))]
  exact min_le_right _ _

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The exact overlap formula for the `ℓ¹` distance of nonnegative summable laws. -/
theorem l1Distance_eq_overlap (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsp : Summable p) (hsq : Summable q) :
    l1Distance p q = (∑' i, p i) + (∑' i, q i) - 2 * ∑' i, min (p i) (q i) := by
  have hmin := summable_min p q hp hq hsq
  unfold l1Distance
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [(hsp.add hsq).tsum_sub (hmin.mul_left 2), hsp.tsum_add hsq, tsum_mul_left]

/-- Discrete Scheffé: pointwise convergence of normalized nonnegative laws
to a normalized law implies convergence in `ℓ¹`. -/
theorem discrete_scheffe (p : ℕ → ι → ℝ) (q : ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∀ n, HasSum (p n) 1) (hqsum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n ↦ p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n ↦ l1Distance (p n) q) atTop (𝓝 0) := by
  have hminpoint i : Tendsto (fun n ↦ min (p n i) (q i)) atTop (𝓝 (q i)) := by
    simpa using (hpoint i).min (tendsto_const_nhds (x := q i))
  have hminlimit : Tendsto (fun n ↦ ∑' i, min (p n i) (q i)) atTop (𝓝 1) := by
    simpa only [hqsum.tsum_eq] using
      (tendsto_tsum_of_dominated_convergence hqsum.summable hminpoint
        (Eventually.of_forall fun n i ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp n i) (hq i))]
          exact min_le_right _ _))
  have hid n : l1Distance (p n) q = 2 - 2 * ∑' i, min (p n i) (q i) := by
    rw [l1Distance_eq_overlap _ _ (hp n) hq (hpsum n).summable hqsum.summable,
      (hpsum n).tsum_eq, hqsum.tsum_eq]
    ring
  simp_rw [hid]
  simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub (hminlimit.const_mul 2)

/-- Countable Cauchy--Schwarz in the square-root form used by Hellinger affinity. -/
theorem affinity_le_sqrt_mass (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsp : Summable p) (hsq : Summable q) :
    affinity p q ≤ Real.sqrt (∑' i, p i) * Real.sqrt (∑' i, q i) := by
  apply Real.tsum_le_of_sum_le (fun i ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  intro s
  calc
    (∑ i ∈ s, Real.sqrt (p i) * Real.sqrt (q i)) ≤
        Real.sqrt (∑ i ∈ s, p i) * Real.sqrt (∑ i ∈ s, q i) :=
      Real.sum_sqrt_mul_sqrt_le s hp hq
    _ ≤ Real.sqrt (∑' i, p i) * Real.sqrt (∑' i, q i) := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt (hsp.sum_le_tsum s (fun i _ ↦ hp i)))
        (Real.sqrt_le_sqrt (hsq.sum_le_tsum s (fun i _ ↦ hq i)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem affinity_summable (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsp : Summable p) (hsq : Summable q) :
    Summable (fun i ↦ Real.sqrt (p i) * Real.sqrt (q i)) := by
  apply (hsp.add hsq).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hx := Real.sq_sqrt (hp i)
  have hy := Real.sq_sqrt (hq i)
  nlinarith [sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i))]

/-- Dimension-free countable affinity continuity; no finite support is required. -/
theorem affinity_l1_continuity (p q r : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hsp : Summable p) (hsq : Summable q) (hrsum : HasSum r 1) :
    |affinity p r - affinity q r| ≤ Real.sqrt (l1Distance p q) := by
  have hpr := affinity_summable p r hp hr hsp hrsum.summable
  have hqr := affinity_summable q r hq hr hsq hrsum.summable
  have hdiff : Summable (fun i ↦ |p i - q i|) := (hsp.sub hsq).abs
  have hbound := affinity_summable (fun i ↦ |p i - q i|) r
    (fun i ↦ abs_nonneg _) hr hdiff hrsum.summable
  unfold affinity
  rw [← hpr.tsum_sub hqr]
  calc
    |∑' i, (Real.sqrt (p i) * Real.sqrt (r i) - Real.sqrt (q i) * Real.sqrt (r i))| ≤
        ∑' i, |Real.sqrt (p i) * Real.sqrt (r i) - Real.sqrt (q i) * Real.sqrt (r i)| := by
      have hnorm : Summable (fun i ↦
          ‖Real.sqrt (p i) * Real.sqrt (r i) - Real.sqrt (q i) * Real.sqrt (r i)‖) := by
        simpa only [Real.norm_eq_abs] using (hpr.sub hqr).abs
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, Real.sqrt |p i - q i| * Real.sqrt (r i) := by
      apply (hpr.sub hqr).abs.tsum_le_tsum _ hbound
      intro i
      rw [← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (Cloning.ClassicalFidelity.sqrt_difference_bound _ _ (hp i) (hq i))
        (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (∑' i, |p i - q i|) * Real.sqrt (∑' i, r i) :=
      affinity_le_sqrt_mass _ _ (fun i ↦ abs_nonneg _) hr hdiff hrsum.summable
    _ = Real.sqrt (l1Distance p q) := by rw [hrsum.tsum_eq, Real.sqrt_one, mul_one]; rfl

/-- Pointwise normalized laws have convergent Hellinger affinities against
every fixed normalized target law, even on an infinite occupation lattice. -/
theorem affinity_tendsto_of_pointwise (p : ℕ → ι → ℝ) (q r : ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hpsum : ∀ n, HasSum (p n) 1) (hqsum : HasSum q 1) (hrsum : HasSum r 1)
    (hpoint : ∀ i, Tendsto (fun n ↦ p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n ↦ affinity (p n) r) atTop (𝓝 (affinity q r)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  apply squeeze_zero (fun n ↦ abs_nonneg _)
    (fun n ↦ affinity_l1_continuity (p n) q r (hp n) hq hr
      (hpsum n).summable hqsum.summable hrsum)
  simpa using (Real.continuous_sqrt.tendsto 0).comp
    (discrete_scheffe p q hp hq hpsum hqsum hpoint)

/-- Both countable probability laws may vary. Pointwise limits and
normalization alone imply convergence of their Hellinger affinity. -/
theorem affinity_tendsto_of_pointwise_two (p q : ℕ → ι → ℝ) (p₀ q₀ : ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ n i, 0 ≤ q n i)
    (hp₀ : ∀ i, 0 ≤ p₀ i) (hq₀ : ∀ i, 0 ≤ q₀ i)
    (hpsum : ∀ n, HasSum (p n) 1) (hqsum : ∀ n, HasSum (q n) 1)
    (hp₀sum : HasSum p₀ 1) (hq₀sum : HasSum q₀ 1)
    (hpointp : ∀ i, Tendsto (fun n ↦ p n i) atTop (𝓝 (p₀ i)))
    (hpointq : ∀ i, Tendsto (fun n ↦ q n i) atTop (𝓝 (q₀ i))) :
    Tendsto (fun n ↦ affinity (p n) (q n)) atTop (𝓝 (affinity p₀ q₀)) := by
  have hpL := discrete_scheffe p p₀ hp hp₀ hpsum hp₀sum hpointp
  have hqL := discrete_scheffe q q₀ hq hq₀ hqsum hq₀sum hpointq
  have hbound n : |affinity (p n) (q n) - affinity p₀ q₀| ≤
      Real.sqrt (l1Distance (p n) p₀) + Real.sqrt (l1Distance (q n) q₀) := by
    apply (abs_sub_le (affinity (p n) (q n)) (affinity p₀ (q n)) (affinity p₀ q₀)).trans
    apply add_le_add
      (affinity_l1_continuity (p n) p₀ (q n) (hp n) hp₀ (hq n)
        (hpsum n).summable hp₀sum.summable (hqsum n))
    rw [affinity_comm p₀ (q n), affinity_comm p₀ q₀]
    exact affinity_l1_continuity (q n) q₀ p₀ (hq n) hq₀ hp₀
      (hqsum n).summable hq₀sum.summable hp₀sum
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  apply squeeze_zero (fun n ↦ abs_nonneg _) hbound
  simpa using ((Real.continuous_sqrt.tendsto 0).comp hpL).add
    ((Real.continuous_sqrt.tendsto 0).comp hqL)

/-- The scalar estimate upgrades `ℓ¹` convergence to square-root amplitude convergence. -/
theorem sqrt_amplitude_error_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
  have h := mul_self_le_mul_self (abs_nonneg (Real.sqrt x - Real.sqrt y))
    (Cloning.ClassicalFidelity.sqrt_difference_bound x y hx hy)
  simpa only [← sq, sq_abs, Real.sq_sqrt (abs_nonneg (x - y))] using h

/-- This is the square-root amplitude limit used in the coherent-product argument. -/
theorem sqrt_amplitudes_tendsto_of_pointwise (p : ℕ → ι → ℝ) (q : ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∀ n, HasSum (p n) 1) (hqsum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n ↦ p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n ↦ ∑' i, (Real.sqrt (p n i) - Real.sqrt (q i)) ^ 2)
      atTop (𝓝 0) := by
  have hs (n : ℕ) : Summable (fun i ↦ (Real.sqrt (p n i) - Real.sqrt (q i)) ^ 2) := by
    apply ((hpsum n).summable.sub hqsum.summable).abs.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sqrt_amplitude_error_le _ _ (hp n i) (hq i)
  apply squeeze_zero (fun n ↦ tsum_nonneg (fun i ↦ sq_nonneg _))
    (fun n ↦ (hs n).tsum_le_tsum
      (fun i ↦ sqrt_amplitude_error_le _ _ (hp n i) (hq i))
      ((hpsum n).summable.sub hqsum.summable).abs)
  exact discrete_scheffe p q hp hq hpsum hqsum hpoint

/-- The thermal normalization is proved in `Thermal`; hence a pointwise
geometric occupation limit already implies the required `ℓ¹` limit. -/
theorem geometric_limit_l1 (p : ℕ → ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hp : ∀ n k, 0 ≤ p n k)
    (hpsum : ∀ n, HasSum (p n) 1)
    (hpoint : ∀ k, Tendsto (fun n ↦ p n k) atTop (𝓝 (Cloning.Thermal.geometric q k))) :
    Tendsto (fun n ↦ l1Distance (p n) (Cloning.Thermal.geometric q)) atTop (𝓝 0) :=
  discrete_scheffe p (Cloning.Thermal.geometric q) hp
    (Cloning.Thermal.geometric_nonneg hq0 hq1.le)
    hpsum (Cloning.Thermal.geometric_hasSum hq0 hq1) hpoint

/-- The product-geometric Fock occupation limit needs no additional tightness
hypothesis: normalization and coordinatewise convergence suffice. -/
theorem multimode_geometric_limit_l1 {s : ℕ}
    (p : ℕ → (Fin s → ℕ) → ℝ) (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hp : ∀ n k, 0 ≤ p n k) (hpsum : ∀ n, HasSum (p n) 1)
    (hpoint : ∀ k, Tendsto (fun n ↦ p n k) atTop
      (𝓝 (∏ i, Cloning.Thermal.geometric (q i) (k i)))) :
    Tendsto (fun n ↦ l1Distance (p n)
      (fun k ↦ ∏ i, Cloning.Thermal.geometric (q i) (k i))) atTop (𝓝 0) := by
  apply discrete_scheffe p _ hp _ hpsum
    (Cloning.Thermal.multimode_geometric_hasSum hq0 hq1) hpoint
  intro k
  exact Finset.prod_nonneg fun i _ ↦ Cloning.Thermal.geometric_nonneg (hq0 i) (hq1 i).le _

end Cloning.CountableScheffe
