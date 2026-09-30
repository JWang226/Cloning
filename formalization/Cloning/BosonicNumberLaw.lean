import Cloning.Thermal
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Seeded bosonic number laws and thermal amplification

The negative-binomial coefficients are normalized and their generating
function is evaluated as a convergent series. Finite binomial convolution
identifies the amplified thermal input law. These are exact scalar formulas;
the separate amplifier module supplies the operator realization.
-/

noncomputable section
open scoped BigOperators Topology

namespace Cloning.BosonicNumberLaw

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Number probabilities for vacuum signal and an idler seed of `l` quanta. -/
def seededLaw (r : ℝ) (l k : ℕ) : ℝ :=
  ((l + k).choose l : ℝ) * (1 - r) ^ (l + 1) * r ^ k

/-- The geometric probability generating function. -/
def pgfBase (r z : ℝ) : ℝ := (1 - r) / (1 - r * z)

theorem seededLaw_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (l k : ℕ) :
    0 ≤ seededLaw r l k := by
  unfold seededLaw
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
    (pow_nonneg hr0 _)

/-- Exact seeded number generating function, including `z=1` and zero noise. -/
theorem seededLaw_pgf_hasSum {r z : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (l : ℕ) :
    HasSum (fun k ↦ seededLaw r l k * z ^ k) (pgfBase r z ^ (l + 1)) := by
  have hrz0 : 0 ≤ r * z := mul_nonneg hr0 hz0
  have hrz1 : r * z < 1 := (mul_le_of_le_one_right hr0 hz1).trans_lt hr1
  have hnorm : ‖r * z‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hrz0]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one l hnorm).mul_left ((1 - r) ^ (l + 1))
  convert hs using 1
  · ext k
    simp only [seededLaw, Nat.add_comm, mul_pow]
    ring
  · simp only [pgfBase, div_pow]
    ring

theorem seededLaw_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (l : ℕ) :
    HasSum (seededLaw r l) 1 := by
  have hne : 1 - r ≠ 0 := by linarith
  simpa only [one_pow, mul_one, pgfBase, div_self hne] using
    seededLaw_pgf_hasSum hr0 hr1 (show (0 : ℝ) ≤ 1 by norm_num) le_rfl l

theorem seededLaw_zero (r : ℝ) (k : ℕ) :
    seededLaw r 0 k = Cloning.Thermal.geometric r k := by
  simp [seededLaw, Cloning.Thermal.geometric]

theorem pgfBase_nonneg {r z : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz1 : z ≤ 1) : 0 ≤ pgfBase r z := by
  unfold pgfBase
  exact div_nonneg (by linarith) (by
    have h := mul_le_of_le_one_right hr0 hz1
    linarith)

theorem pgfBase_le_one {r z : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz1 : z ≤ 1) : pgfBase r z ≤ 1 := by
  have hmul := mul_le_of_le_one_right hr0 hz1
  have hden : 0 < 1 - r * z := by linarith
  exact (div_le_one hden).mpr (by linarith)

/-- Every seeded exponential moment is bounded by the vacuum-idler moment. -/
theorem seededLaw_moment_le {r z : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (l : ℕ) :
    (∑' k, seededLaw r l k * z ^ k) ≤ pgfBase r z := by
  rw [(seededLaw_pgf_hasSum hr0 hr1 hz0 hz1 l).tsum_eq]
  have h0 := pgfBase_nonneg hr0 hr1 hz1
  have h1 := pgfBase_le_one hr0 hr1 hz1
  induction l with
  | zero => simp
  | succ l ih =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right ih h0).trans (mul_le_of_le_one_right h0 h1)

/-- The output number transition, padded by zero below the input number. -/
def transition (r : ℝ) (n t : ℕ) : ℝ :=
  if n ≤ t then seededLaw r n (t - n) else 0

def thermalOutput (r q : ℝ) (t : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (t + 1), Cloning.Thermal.geometric q n * seededLaw r n (t - n)

/-- Binomial convolution proves the actual thermal-input output probabilities. -/
theorem thermalOutput_eq (r q : ℝ) (t : ℕ) :
    thermalOutput r q t = Cloning.Thermal.geometric (r + (1 - r) * q) t := by
  have he : 1 - (r + (1 - r) * q) = (1 - q) * (1 - r) := by ring
  have hb : r + (1 - r) * q = q * (1 - r) + r := by ring
  rw [thermalOutput, Cloning.Thermal.geometric, he, hb, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnt : n ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [seededLaw, show n + (t - n) = t by omega, Cloning.Thermal.geometric,
    pow_succ, mul_pow]
  ring

theorem thermalOutput_eq_tsum (r q : ℝ) (t : ℕ) :
    thermalOutput r q t = ∑' n, Cloning.Thermal.geometric q n * transition r n t := by
  rw [tsum_eq_sum (s := Finset.range (t + 1))]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [transition, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  · intro n hn
    have hnt : ¬ n ≤ t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp only [transition, if_neg hnt, mul_zero]

/-- In gain notation the derived parameter is exactly the manuscript's
`q ↦ 1-(1-q)/g`. -/
theorem thermalOutput_gain (g q : ℝ) (t : ℕ) :
    thermalOutput (1 - 1 / g) q t = Cloning.Thermal.geometric (Cloning.Thermal.amplified g q) t := by
  rw [thermalOutput_eq]
  congr 1
  unfold Cloning.Thermal.amplified
  ring

def productLaw {s : ℕ} (r : Fin s → ℝ) (l k : Fin s → ℕ) : ℝ :=
  ∏ i, seededLaw (r i) (l i) (k i)

def productTest {s : ℕ} (z : Fin s → ℝ) (k : Fin s → ℕ) : ℝ := ∏ i, z i ^ k i

theorem productLaw_nonneg {s : ℕ} {r : Fin s → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (l k : Fin s → ℕ) :
    0 ≤ productLaw r l k :=
  Finset.prod_nonneg (fun i _ ↦ seededLaw_nonneg (hr0 i) (hr1 i) _ _)

theorem productLaw_hasSum {s : ℕ} {r : Fin s → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (l : Fin s → ℕ) :
    HasSum (productLaw r l) 1 := by
  simpa only [productLaw, Finset.prod_const_one] using
    Cloning.Thermal.hasSum_fin_product s (fun i k ↦ seededLaw (r i) (l i) k)
      (fun _ ↦ 1) (fun i k ↦ seededLaw_nonneg (hr0 i) (hr1 i) _ _)
      (fun i ↦ seededLaw_hasSum (hr0 i) (hr1 i) _)

/-- Exact joint generating function for an arbitrary fixed idler number tuple. -/
theorem productLaw_pgf_hasSum {s : ℕ} {r z : Fin s → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (l : Fin s → ℕ) :
    HasSum (fun k ↦ productLaw r l k * productTest z k)
      (∏ i, pgfBase (r i) (z i) ^ (l i + 1)) := by
  simpa only [productLaw, productTest, Finset.prod_mul_distrib] using
    Cloning.Thermal.hasSum_fin_product s
      (fun i k ↦ seededLaw (r i) (l i) k * z i ^ k)
      (fun i ↦ pgfBase (r i) (z i) ^ (l i + 1))
      (fun i k ↦ mul_nonneg (seededLaw_nonneg (hr0 i) (hr1 i) _ _) (pow_nonneg (hz0 i) _))
      (fun i ↦ seededLaw_pgf_hasSum (hr0 i) (hr1 i) (hz0 i) (hz1 i) _)

/-- Multimode least-noise exponential moment for every idler seed. -/
theorem productLaw_moment_le {s : ℕ} {r z : Fin s → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (l : Fin s → ℕ) :
    (∑' k, productLaw r l k * productTest z k) ≤ ∏ i, pgfBase (r i) (z i) := by
  rw [(productLaw_pgf_hasSum hr0 hr1 hz0 hz1 l).tsum_eq]
  apply Finset.prod_le_prod
  · intro i hi
    exact pow_nonneg (pgfBase_nonneg (hr0 i) (hr1 i) (hz1 i)) _
  · intro i hi
    rw [← (seededLaw_pgf_hasSum (hr0 i) (hr1 i) (hz0 i) (hz1 i) (l i)).tsum_eq]
    exact seededLaw_moment_le (hr0 i) (hr1 i) (hz0 i) (hz1 i) (l i)

theorem productTest_nonneg {s : ℕ} {z : Fin s → ℝ} (hz0 : ∀ i, 0 ≤ z i)
    (k : Fin s → ℕ) : 0 ≤ productTest z k :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hz0 i) _)

theorem productTest_le_one {s : ℕ} {z : Fin s → ℝ} (hz0 : ∀ i, 0 ≤ z i)
    (hz1 : ∀ i, z i ≤ 1) (k : Fin s → ℕ) : productTest z k ≤ 1 := by
  apply Finset.prod_le_one
  · intro i hi; exact pow_nonneg (hz0 i) _
  · intro i hi; exact pow_le_one₀ (hz0 i) (hz1 i)

/-- Arbitrarily correlated idler-number mixing; no product assumption on `a`. -/
def mixtureLaw {s : ℕ} (r : Fin s → ℝ) (a : (Fin s → ℕ) → ℝ)
    (k : Fin s → ℕ) : ℝ := ∑' l, a l * productLaw r l k

theorem mixtureLaw_nonneg {s : ℕ} {r : Fin s → ℝ} {a : (Fin s → ℕ) → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (ha0 : ∀ l, 0 ≤ a l)
    (k : Fin s → ℕ) : 0 ≤ mixtureLaw r a k :=
  tsum_nonneg (fun l ↦ mul_nonneg (ha0 l) (productLaw_nonneg hr0 hr1 l k))

theorem mixtureJoint_summable {s : ℕ} {r : Fin s → ℝ} {a : (Fin s → ℕ) → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (ha0 : ∀ l, 0 ≤ a l)
    (ha : Summable a) :
    Summable (fun lk : (Fin s → ℕ) × (Fin s → ℕ) ↦ a lk.1 * productLaw r lk.1 lk.2) := by
  apply (summable_prod_of_nonneg (fun lk ↦
    mul_nonneg (ha0 lk.1) (productLaw_nonneg hr0 hr1 _ _))).mpr
  refine ⟨fun l ↦ (productLaw_hasSum hr0 hr1 l).summable.mul_left (a l), ?_⟩
  convert ha using 1
  ext l
  change (∑' k, a l * productLaw r l k) = a l
  rw [tsum_mul_left, (productLaw_hasSum hr0 hr1 l).tsum_eq, mul_one]

/-- The correlated output law has exactly the idler's total mass. -/
theorem mixtureLaw_hasSum {s : ℕ} {r : Fin s → ℝ} {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (ha0 : ∀ l, 0 ≤ a l)
    (ha : HasSum a c) : HasSum (mixtureLaw r a) c := by
  have hs := mixtureJoint_summable hr0 hr1 ha0 ha.summable
  have hcol : Summable (mixtureLaw r a) := hs.prod_symm.prod
  have heq : (∑' k, mixtureLaw r a k) = c := by
    unfold mixtureLaw
    rw [hs.tsum_comm (f := fun l k ↦ a l * productLaw r l k)]
    simp_rw [tsum_mul_left, (productLaw_hasSum hr0 hr1 _).tsum_eq, mul_one]
    exact ha.tsum_eq
  rw [← heq]
  exact hcol.hasSum

/-- Exact correlated-mixture generating function, with Fubini justified by
summability of the actual nonnegative joint law. -/
theorem mixtureLaw_pgf_eq {s : ℕ} {r z : Fin s → ℝ} {a : (Fin s → ℕ) → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : Summable a) :
    (∑' k, mixtureLaw r a k * productTest z k) =
      ∑' l, a l * ∏ i, pgfBase (r i) (z i) ^ (l i + 1) := by
  have hs := mixtureJoint_summable hr0 hr1 ha0 ha
  have hw : Summable (fun lk : (Fin s → ℕ) × (Fin s → ℕ) ↦
      a lk.1 * productLaw r lk.1 lk.2 * productTest z lk.2) := by
    apply hs.of_norm_bounded
    intro lk
    have hp := mul_nonneg (ha0 lk.1) (productLaw_nonneg hr0 hr1 lk.1 lk.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (productTest_nonneg hz0 _))]
    exact mul_le_of_le_one_right hp (productTest_le_one hz0 hz1 _)
  unfold mixtureLaw
  simp_rw [← tsum_mul_right]
  rw [hw.tsum_comm (f := fun l k ↦ a l * productLaw r l k * productTest z k)]
  simp_rw [mul_assoc, tsum_mul_left, (productLaw_pgf_hasSum hr0 hr1 hz0 hz1 _).tsum_eq]

/-- The least-noise exponential-moment inequality for any correlated idler
mixing law, including deficient total mass `c`. -/
theorem mixtureLaw_moment_le {s : ℕ} {r z : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c) :
    (∑' k, mixtureLaw r a k * productTest z k) ≤ c * ∏ i, pgfBase (r i) (z i) := by
  rw [mixtureLaw_pgf_eq hr0 hr1 hz0 hz1 ha0 ha.summable]
  have hM0 (l : Fin s → ℕ) : 0 ≤ ∏ i, pgfBase (r i) (z i) ^ (l i + 1) :=
    Finset.prod_nonneg (fun i _ ↦ pow_nonneg (pgfBase_nonneg (hr0 i) (hr1 i) (hz1 i)) _)
  have hM (l : Fin s → ℕ) : (∏ i, pgfBase (r i) (z i) ^ (l i + 1)) ≤
      ∏ i, pgfBase (r i) (z i) := by
    rw [← (productLaw_pgf_hasSum hr0 hr1 hz0 hz1 l).tsum_eq]
    exact productLaw_moment_le hr0 hr1 hz0 hz1 l
  have hmajor := ha.summable.mul_right (∏ i, pgfBase (r i) (z i))
  have hminor : Summable (fun l ↦ a l * ∏ i, pgfBase (r i) (z i) ^ (l i + 1)) := by
    apply hmajor.of_norm_bounded
    intro l
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0 l) (hM0 l))]
    exact mul_le_mul_of_nonneg_left (hM l) (ha0 l)
  calc
    _ ≤ ∑' l, a l * ∏ i, pgfBase (r i) (z i) :=
      hminor.tsum_le_tsum (fun l ↦ mul_le_mul_of_nonneg_left (hM l) (ha0 l)) hmajor
    _ = _ := by rw [tsum_mul_right, ha.tsum_eq]

/-- Exact seeded expectation of the thermal fidelity witness. -/
theorem seededLaw_witness_hasSum {q x : ℝ} (hq0 : 0 < q) (hqx : q < x)
    (hx1 : x < 1) (l : ℕ) :
    HasSum (fun k ↦ seededLaw x l k * Cloning.Thermal.witness q x k)
      (Real.sqrt ((1 - q) / (1 - x)) * pgfBase x (Real.sqrt (q / x)) ^ (l + 1)) := by
  have hx0 : 0 < x := hq0.trans hqx
  have hz1 : Real.sqrt (q / x) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hx0).mpr hqx.le)
  convert (seededLaw_pgf_hasSum hx0.le hx1 (Real.sqrt_nonneg _) hz1 l).mul_left
    (Real.sqrt ((1 - q) / (1 - x))) using 1
  ext k
  rw [Cloning.Thermal.witness_closed hq0.le (hqx.trans hx1) hx0.le hx1]
  ring

/-- The vacuum prefactor is identified by uniqueness of the two convergent
series, avoiding an additional algebraic assumption about the witness. -/
theorem witness_pgfBase_eq_fidelity {q x : ℝ} (hq0 : 0 < q) (hqx : q < x)
    (hx1 : x < 1) :
    Real.sqrt ((1 - q) / (1 - x)) * pgfBase x (Real.sqrt (q / x)) =
      Cloning.Thermal.fidelity q x := by
  have h := seededLaw_witness_hasSum hq0 hqx hx1 0
  simp only [seededLaw_zero, zero_add, pow_one] at h
  exact h.unique (Cloning.Thermal.witness_moment_hasSum hq0 (hqx.trans hx1)
    (hq0.trans hqx) hx1)

theorem seededLaw_witness_moment_le {q x : ℝ} (hq0 : 0 < q) (hqx : q < x)
    (hx1 : x < 1) (l : ℕ) :
    (∑' k, seededLaw x l k * Cloning.Thermal.witness q x k) ≤
      Cloning.Thermal.fidelity q x := by
  have hx0 := hq0.trans hqx
  have hz1 : Real.sqrt (q / x) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hx0).mpr hqx.le)
  rw [(seededLaw_witness_hasSum hq0 hqx hx1 l).tsum_eq,
    ← witness_pgfBase_eq_fidelity hq0 hqx hx1]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [← (seededLaw_pgf_hasSum hx0.le hx1 (Real.sqrt_nonneg _) hz1 l).tsum_eq]
  exact seededLaw_moment_le hx0.le hx1 (Real.sqrt_nonneg _) hz1 l

/-- The exact product thermal witness obeys the least-noise bound for every
correlated countable idler law. Deficient mass is allowed. -/
theorem mixtureLaw_witness_moment_le {s : ℕ} {q x : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c) :
    (∑' k, mixtureLaw x a k * ∏ i, Cloning.Thermal.witness (q i) (x i) (k i)) ≤
      c * ∏ i, Cloning.Thermal.fidelity (q i) (x i) := by
  let C : ℝ := ∏ i, Real.sqrt ((1 - q i) / (1 - x i))
  let z : Fin s → ℝ := fun i ↦ Real.sqrt (q i / x i)
  have hx0 (i) : 0 < x i := (hq0 i).trans (hqx i)
  have hz0 (i) : 0 ≤ z i := Real.sqrt_nonneg _
  have hz1 (i) : z i ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one (hx0 i)).mpr (hqx i).le)
  have hC : 0 ≤ C := Finset.prod_nonneg (fun i _ ↦ Real.sqrt_nonneg _)
  have hterm (k : Fin s → ℕ) :
      (∏ i, Cloning.Thermal.witness (q i) (x i) (k i)) = C * productTest z k := by
    simp only [Cloning.Thermal.witness_closed (hq0 _).le ((hqx _).trans (hx1 _))
      (hx0 _).le (hx1 _), Finset.prod_mul_distrib, C, productTest, z]
  simp_rw [hterm, ← mul_assoc, mul_right_comm (mixtureLaw x a _) C]
  rw [tsum_mul_right]
  calc
    _ ≤ (c * ∏ i, pgfBase (x i) (z i)) * C :=
      mul_le_mul_of_nonneg_right
        (mixtureLaw_moment_le (fun i ↦ (hx0 i).le) hx1 hz0 hz1 ha0 ha) hC
    _ = _ := by
      rw [mul_assoc, mul_comm (∏ i, pgfBase (x i) (z i)) C, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact witness_pgfBase_eq_fidelity (hq0 i) (hqx i) (hx1 i)

end Cloning.BosonicNumberLaw
