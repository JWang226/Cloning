import Cloning.BosonicStochasticOrder

/-!
# Correlated multimode least-noise moments

Products of arbitrary nonnegative decreasing number tests satisfy the full
least-noise inequality for the actual negative-binomial output law, even when
the idler occupation law is correlated and has deficient total mass.
-/

noncomputable section
open scoped BigOperators Topology
namespace Cloning.BosonicStochasticOrder

open Cloning BosonicNumberLaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Exact factorization of the seeded expectation of a product test. -/
theorem productLaw_antitone_weighted_hasSum {s : ℕ} {r : Fin s → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) {w : Fin s → ℕ → ℝ}
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (l : Fin s → ℕ) :
    HasSum (fun k ↦ productLaw r l k * ∏ i, w i (k i))
      (∏ i, ∑' k, seededLaw (r i) (l i) k * w i k) := by
  simpa only [productLaw, Finset.prod_mul_distrib] using
    Thermal.hasSum_fin_product s (fun i k ↦ seededLaw (r i) (l i) k * w i k)
      (fun i ↦ ∑' k, seededLaw (r i) (l i) k * w i k)
      (fun i k ↦ mul_nonneg (seededLaw_nonneg (hr0 i) (hr1 i) _ _) (hw0 i k))
      (fun i ↦ (seededLaw_weighted_summable (hr0 i) (hr1 i) (hw0 i) (hw i) (l i)).hasSum)

/-- Full fixed-seed multimode least-noise bound. -/
theorem productLaw_antitone_moment_le {s : ℕ} {r : Fin s → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) {w : Fin s → ℕ → ℝ}
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i)) (l : Fin s → ℕ) :
    (∑' k, productLaw r l k * ∏ i, w i (k i)) ≤
      ∏ i, ∑' k, Thermal.geometric (r i) k * w i k := by
  rw [(productLaw_antitone_weighted_hasSum hr0 hr1 hw0 hw l).tsum_eq]
  apply Finset.prod_le_prod
  · intro i hi
    exact tsum_nonneg (fun k ↦ mul_nonneg (seededLaw_nonneg (hr0 i) (hr1 i) _ _) (hw0 i k))
  · intro i hi
    exact seededLaw_antitone_moment_le (hr0 i) (hr1 i) (hw0 i) (hw i) (l i)

/-- The actual correlated output has an absolutely convergent product-test
expectation; boundedness is derived from antitonicity. -/
theorem mixtureLaw_antitone_weighted_summable {s : ℕ} {r : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {w : Fin s → ℕ → ℝ} (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (ha0 : ∀ l, 0 ≤ a l) (ha : Summable a) :
    Summable (fun k ↦ mixtureLaw r a k * ∏ i, w i (k i)) := by
  have hs := (mixtureLaw_hasSum hr0 hr1 ha0 ha.hasSum).summable
  apply (hs.mul_right (∏ i, w i 0)).of_norm_bounded
  intro k
  have hm := mixtureLaw_nonneg hr0 hr1 ha0 k
  have hwk : 0 ≤ ∏ i, w i (k i) := Finset.prod_nonneg (fun i _ ↦ hw0 i _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm hwk)]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ ↦ hw0 i _) (fun i _ ↦ hw i (Nat.zero_le _))) hm

/-- Fubini for the full product-test expectation of the correlated output law. -/
theorem mixtureLaw_antitone_moment_eq {s : ℕ} {r : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    {w : Fin s → ℕ → ℝ} (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (ha0 : ∀ l, 0 ≤ a l) (ha : Summable a) :
    (∑' k, mixtureLaw r a k * ∏ i, w i (k i)) =
      ∑' l, a l * ∏ i, ∑' k, seededLaw (r i) (l i) k * w i k := by
  have hs := mixtureJoint_summable hr0 hr1 ha0 ha
  have hW0 (k : Fin s → ℕ) : 0 ≤ ∏ i, w i (k i) :=
    Finset.prod_nonneg (fun i _ ↦ hw0 i _)
  have hW (k : Fin s → ℕ) : (∏ i, w i (k i)) ≤ ∏ i, w i 0 := by
    exact Finset.prod_le_prod (fun i _ ↦ hw0 i _) (fun i _ ↦ hw i (Nat.zero_le _))
  have hsW : Summable (fun lk : (Fin s → ℕ) × (Fin s → ℕ) ↦
      a lk.1 * productLaw r lk.1 lk.2 * ∏ i, w i (lk.2 i)) := by
    apply (hs.mul_right (∏ i, w i 0)).of_norm_bounded
    intro lk
    have hnonneg := mul_nonneg (ha0 lk.1) (productLaw_nonneg hr0 hr1 lk.1 lk.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnonneg (hW0 _))]
    exact mul_le_mul_of_nonneg_left (hW _) hnonneg
  unfold mixtureLaw
  simp_rw [← tsum_mul_right]
  rw [hsW.tsum_comm (f := fun l k ↦ a l * productLaw r l k * ∏ i, w i (k i))]
  simp_rw [mul_assoc, tsum_mul_left,
    (productLaw_antitone_weighted_hasSum hr0 hr1 hw0 hw _).tsum_eq]

/-- The manuscript's complete scalar least-noise test class: every product of
bounded nonnegative nonincreasing number functions, under arbitrary correlated
idler occupation weights, with the exact total-mass factor. -/
theorem mixtureLaw_antitone_moment_le {s : ℕ} {r : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) {w : Fin s → ℕ → ℝ}
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c) :
    (∑' k, mixtureLaw r a k * ∏ i, w i (k i)) ≤
      c * ∏ i, ∑' k, Thermal.geometric (r i) k * w i k := by
  rw [mixtureLaw_antitone_moment_eq hr0 hr1 hw0 hw ha0 ha.summable]
  have hM0 (l : Fin s → ℕ) :
      0 ≤ ∏ i, ∑' k, seededLaw (r i) (l i) k * w i k :=
    Finset.prod_nonneg (fun i _ ↦ tsum_nonneg
      (fun k ↦ mul_nonneg (seededLaw_nonneg (hr0 i) (hr1 i) _ _) (hw0 i k)))
  have hM (l : Fin s → ℕ) :
      (∏ i, ∑' k, seededLaw (r i) (l i) k * w i k) ≤
        ∏ i, ∑' k, Thermal.geometric (r i) k * w i k := by
    rw [← (productLaw_antitone_weighted_hasSum hr0 hr1 hw0 hw l).tsum_eq]
    exact productLaw_antitone_moment_le hr0 hr1 hw0 hw l
  have hmajor := ha.summable.mul_right (∏ i, ∑' k, Thermal.geometric (r i) k * w i k)
  have hminor : Summable (fun l ↦ a l * ∏ i, ∑' k, seededLaw (r i) (l i) k * w i k) := by
    apply hmajor.of_norm_bounded
    intro l
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0 l) (hM0 l))]
    exact mul_le_mul_of_nonneg_left (hM l) (ha0 l)
  calc
    _ ≤ ∑' l, a l * ∏ i, ∑' k, Thermal.geometric (r i) k * w i k :=
      hminor.tsum_le_tsum (fun l ↦ mul_le_mul_of_nonneg_left (hM l) (ha0 l)) hmajor
    _ = _ := by rw [tsum_mul_right, ha.tsum_eq]

/-- The same result written directly as comparison with the product geometric
vacuum-output law, matching the two expectations in the least-noise proposition. -/
theorem mixtureLaw_antitone_moment_le_geometric {s : ℕ} {r : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) {w : Fin s → ℕ → ℝ}
    (hw0 : ∀ i k, 0 ≤ w i k) (hw : ∀ i, Antitone (w i))
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c) :
    (∑' k, mixtureLaw r a k * ∏ i, w i (k i)) ≤
      c * ∑' k : Fin s → ℕ, (∏ i, Thermal.geometric (r i) (k i)) * ∏ i, w i (k i) := by
  have hs := productLaw_antitone_weighted_hasSum hr0 hr1 hw0 hw (fun _ ↦ 0)
  simp only [productLaw, seededLaw_zero] at hs
  rw [hs.tsum_eq]
  exact mixtureLaw_antitone_moment_le hr0 hr1 hw0 hw ha0 ha

/-- One-mode correlated-seed notation, convenient for the actual idler channel. -/
theorem single_mixture_antitone_moment_le {r c : ℝ} {a w : ℕ → ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hw0 : ∀ k, 0 ≤ w k) (hw : Antitone w)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c) :
    (∑' k, (∑' l, a l * seededLaw r l k) * w k) ≤
      c * ∑' k, Thermal.geometric r k * w k := by
  let e : (Fin 1 → ℕ) ≃ ℕ := Equiv.funUnique (Fin 1) ℕ
  have he (l : Fin 1 → ℕ) : e l = l 0 := rfl
  have ha' : HasSum (fun l : Fin 1 → ℕ ↦ a (l 0)) c := by
    simpa only [Function.comp_apply, he] using e.hasSum_iff.mpr ha
  have h := mixtureLaw_antitone_moment_le (r := fun _ : Fin 1 ↦ r)
    (w := fun _ ↦ w) (a := fun l ↦ a (l 0))
    (fun _ ↦ hr0) (fun _ ↦ hr1) (fun _ ↦ hw0) (fun _ ↦ hw)
    (fun l ↦ ha0 (l 0)) ha'
  simp only [mixtureLaw, productLaw, Fin.prod_univ_one] at h
  have hinner (k : ℕ) : (∑' l : Fin 1 → ℕ, a (l 0) * seededLaw r (l 0) k) =
      ∑' l, a l * seededLaw r l k := e.tsum_eq (fun l ↦ a l * seededLaw r l k)
  simp_rw [hinner] at h
  have houter := e.tsum_eq (fun k ↦ (∑' l, a l * seededLaw r l k) * w k)
  rw [show (∑' k : Fin 1 → ℕ, (∑' l, a l * seededLaw r l (k 0)) * w (k 0)) =
      (∑' k, (∑' l, a l * seededLaw r l k) * w k) from houter] at h
  exact h

end Cloning.BosonicStochasticOrder
