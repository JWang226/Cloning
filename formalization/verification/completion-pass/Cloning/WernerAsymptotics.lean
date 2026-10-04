import Cloning.Occupation
import Cloning.CountableScheffe
import Cloning.WernerNormalization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Werner occupation asymptotics

The binomial occupation coefficients are shown to converge from the actual
cloning-ratio hypothesis.  The asymptotic probability law is not an assumption.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.WernerAsymptotics

/-- The coefficient for `s` excitation modes (ambient dimension `s+1`). -/
def coefficient (n m s t : ℕ) : ℝ :=
  ((m - t).choose n : ℝ) / ((m + s).choose (n + s) : ℝ)

theorem coefficient_eq_wernerWeight (n m s t : ℕ) :
    coefficient n m s t = Occupation.wernerWeight n m (s + 1) t := by
  simp [coefficient, Occupation.wernerWeight, Nat.add_sub_assoc]

/-- Normalizing affine functions by `n` reduces every fixed-shift ratio to
the given cloning ratio. -/
theorem affine_ratio_tendsto (m : ℕ → ℕ) {γ : ℝ}
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ))
    (a b c d e f : ℝ) (hden : d * γ + e ≠ 0) :
    Tendsto (fun n ↦ (a * (m n : ℝ) + b * n + c) /
      (d * (m n : ℝ) + e * n + f)) atTop (𝓝 ((a * γ + b) / (d * γ + e))) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hnum : Tendsto (fun n ↦ a * ((m n : ℝ) / n) + b + c * (n : ℝ)⁻¹)
      atTop (𝓝 (a * γ + b)) := by
    simpa using ((h.const_mul a).add_const b).add (hn.const_mul c)
  have hden' : Tendsto (fun n ↦ d * ((m n : ℝ) / n) + e + f * (n : ℝ)⁻¹)
      atTop (𝓝 (d * γ + e)) := by
    simpa using ((h.const_mul d).add_const e).add (hn.const_mul f)
  apply (hnum.div hden' hden).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  dsimp
  field_simp

theorem difference_tendsto_atTop (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ (m n : ℝ) - n) atTop atTop := by
  have hprod := (h.sub_const 1).pos_mul_atTop (sub_pos.mpr hγ)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- Every fixed occupation is eventually inside the true finite support. -/
theorem eventually_add_le (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) (t : ℕ) :
    ∀ᶠ n in atTop, n + t ≤ m n := by
  filter_upwards [(difference_tendsto_atTop m hγ h).eventually_ge_atTop (t : ℝ)] with n hn
  have ht : (n : ℝ) + t ≤ m n := by linarith
  exact_mod_cast ht

theorem output_tendsto_atTop (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto m atTop atTop := by
  apply tendsto_atTop_mono' _ _ tendsto_id
  filter_upwards [eventually_add_le m hγ h 0] with n hn
  simpa using hn

theorem coefficient_zero_zero (n m : ℕ) (hnm : n ≤ m) :
    coefficient n m 0 0 = 1 := by
  have hc : (m.choose n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos hnm))
  simp [coefficient, hc]

theorem coefficient_succ_modes (n m s t : ℕ) (hnm : n ≤ m) :
    coefficient n m (s + 1) t = coefficient n m s t *
      ((n : ℝ) + s + 1) / ((m : ℝ) + s + 1) := by
  have hc : ((m + s).choose (n + s) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (by omega)))
  have hc' : ((m + (s + 1)).choose (n + (s + 1)) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (by omega)))
  have hm : (m : ℝ) + s + 1 ≠ 0 := by positivity
  have hchoose : ((m : ℝ) + s + 1) * ((m + s).choose (n + s) : ℝ) =
      ((m + (s + 1)).choose (n + (s + 1)) : ℝ) * ((n : ℝ) + s + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq (m + s) (n + s)
  unfold coefficient
  field_simp
  nlinarith [hchoose]

theorem coefficient_succ_total (n m s t : ℕ) (ht : n + t + 1 ≤ m) :
    coefficient n m s (t + 1) = coefficient n m s t *
      ((m : ℝ) - t - n) / ((m : ℝ) - t) := by
  have hnm : n ≤ m := by omega
  have hc : ((m + s).choose (n + s) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (by omega)))
  have hm : (m : ℝ) - t ≠ 0 := by
    have hmt : (t : ℝ) < m := by exact_mod_cast (by omega : t < m)
    linarith
  have hchoose := Nat.choose_mul_succ_eq (m - (t + 1)) n
  have hsucc : m - (t + 1) + 1 = m - t := by omega
  rw [hsucc] at hchoose
  have hchoose' : ((m - (t + 1)).choose n : ℝ) * ((m : ℝ) - t) =
      ((m - t).choose n : ℝ) * ((m : ℝ) - t - n) := by
    have hcast : ((m - t : ℕ) : ℝ) = (m : ℝ) - t := Nat.cast_sub (by omega)
    have hcast' : ((m - t - n : ℕ) : ℝ) = (m : ℝ) - t - n := by
      rw [Nat.cast_sub (by omega), hcast]
    simpa only [Nat.cast_mul, hcast, hcast'] using congrArg (Nat.cast (R := ℝ)) hchoose
  unfold coefficient
  field_simp
  nlinarith [hchoose']

/-- The vacuum coefficient converges to the thermal vacuum probability. -/
theorem coefficient_vacuum_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) (s : ℕ) :
    Tendsto (fun n ↦ coefficient n (m n) s 0) atTop (𝓝 ((1 / γ) ^ s)) := by
  have hγ0 : γ ≠ 0 := by linarith
  induction s with
  | zero =>
      apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
      filter_upwards [eventually_add_le m hγ h 0] with n hn
      simpa using (coefficient_zero_zero n (m n) (by omega)).symm
  | succ s ih =>
      have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + s + 1) / ((m n : ℝ) + s + 1))
          atTop (𝓝 (1 / γ)) := by
        simpa only [zero_mul, zero_add, one_mul, mul_zero, add_zero, add_assoc] using
          affine_ratio_tendsto m h 0 1 ((s : ℝ) + 1) 1 0 ((s : ℝ) + 1) (by simpa using hγ0)
      have hmul := ih.mul hratio
      rw [← pow_succ] at hmul
      apply hmul.congr'
      filter_upwards [eventually_add_le m hγ h 0] with n hn
      rw [coefficient_succ_modes n (m n) s 0 (by omega)]
      simp only [mul_div_assoc]

/-- The actual Werner binomial ratio tends to a product-geometric coefficient. -/
theorem coefficient_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) (s t : ℕ) :
    Tendsto (fun n ↦ coefficient n (m n) s t) atTop
      (𝓝 ((1 / γ) ^ s * ((γ - 1) / γ) ^ t)) := by
  have hγ0 : γ ≠ 0 := by linarith
  induction t with
  | zero => simpa using coefficient_vacuum_tendsto m hγ h s
  | succ t ih =>
      have hratio : Tendsto (fun n ↦ ((m n : ℝ) - t - n) / ((m n : ℝ) - t))
          atTop (𝓝 ((γ - 1) / γ)) := by
        convert affine_ratio_tendsto m h 1 (-1) (-(t : ℝ)) 1 0 (-(t : ℝ))
          (by simpa using hγ0) using 1 <;> simp only [one_mul, zero_mul, add_zero]
        · ext n; ring
        · simp only [sub_eq_add_neg]
      have hmul := ih.mul hratio
      have heq : (1 / γ) ^ s * ((γ - 1) / γ) ^ t * ((γ - 1) / γ) =
          (1 / γ) ^ s * ((γ - 1) / γ) ^ (t + 1) := by rw [pow_succ, mul_assoc]
      rw [heq] at hmul
      apply hmul.congr'
      filter_upwards [eventually_add_le m hγ h (t + 1)] with n hn
      rw [coefficient_succ_total n (m n) s t (by omega)]
      simp only [mul_div_assoc]

/-- The limiting normalized product of geometric occupation laws. -/
def thermalLaw (γ : ℝ) (s : ℕ) (k : Fin s → ℕ) : ℝ :=
  ∏ i, Thermal.geometric ((γ - 1) / γ) (k i)

theorem thermalLaw_eq (γ : ℝ) (hγ : γ ≠ 0) (s : ℕ) (k : Fin s → ℕ) :
    thermalLaw γ s k = (1 / γ) ^ s * ((γ - 1) / γ) ^ (∑ i, k i) := by
  have hsub : 1 - (γ - 1) / γ = 1 / γ := by field_simp; ring
  simp only [thermalLaw, Thermal.geometric, hsub, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]

theorem thermalLaw_nonneg {γ : ℝ} (hγ : 1 < γ) (s : ℕ) (k : Fin s → ℕ) :
    0 ≤ thermalLaw γ s k := by
  have hγpos : 0 < γ := by linarith
  apply Finset.prod_nonneg
  intro i hi
  apply Thermal.geometric_nonneg (div_nonneg (by linarith) hγpos.le)
  exact (div_le_one hγpos).mpr (by linarith)

theorem thermalLaw_hasSum {γ : ℝ} (hγ : 1 < γ) (s : ℕ) :
    HasSum (thermalLaw γ s) 1 := by
  have hγpos : 0 < γ := by linarith
  apply Thermal.multimode_geometric_hasSum
  · intro i; exact div_nonneg (by linarith) hγpos.le
  · intro i; exact (div_lt_one hγpos).mpr (by linarith)

/-- The padded finite-dimensional Werner occupation law has the claimed
pointwise thermal limit, derived solely from the cloning-ratio limit. -/
theorem occupationLaw_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ))
    (s : ℕ) (k : Fin s → ℕ) :
    Tendsto (fun n ↦ WernerNormalization.occupationLaw n (m n) s k)
      atTop (𝓝 (thermalLaw γ s k)) := by
  rw [thermalLaw_eq γ (by linarith)]
  apply (coefficient_tendsto m hγ h s (∑ i, k i)).congr'
  filter_upwards [eventually_add_le m hγ h (∑ i, k i)] with n hn
  rw [WernerNormalization.occupationLaw, if_pos (by omega)]
  exact coefficient_eq_wernerWeight n (m n) s (∑ i, k i)

/-- The Werner occupation law converges in `ℓ¹` to the normalized multimode
thermal law. Both pointwise convergence and normalization are proved here;
no limit or probability-normalization hypothesis is supplied by the caller.
The cloning inequality `n ≤ m n` is needed only eventually and is derived. -/
theorem occupationLaw_l1_tendsto (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ))
    (s : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun n ↦ CountableScheffe.l1Distance
      (WernerNormalization.occupationLaw n (m n) s) (thermalLaw γ s))
      atTop (𝓝 0) := by
  let p : ℕ → (Fin s → ℕ) → ℝ := fun n k ↦
    if n ≤ m n then WernerNormalization.occupationLaw n (m n) s k
    else thermalLaw γ s k
  have hevent : ∀ᶠ n in atTop, n ≤ m n := by
    simpa only [Nat.add_zero] using eventually_add_le m hγ h 0
  have hp : ∀ n k, 0 ≤ p n k := by
    intro n k
    dsimp [p]
    split_ifs
    · exact WernerNormalization.occupationLaw_nonneg n (m n) s k
    · exact thermalLaw_nonneg hγ s k
  have hpsum : ∀ n, HasSum (p n) 1 := by
    intro n
    by_cases hn : n ≤ m n
    · simpa only [p, if_pos hn] using
        WernerNormalization.occupationLaw_hasSum n (m n) s hn hs
    · simpa only [p, if_neg hn] using thermalLaw_hasSum hγ s
  have hpoint : ∀ k, Tendsto (fun n ↦ p n k) atTop (𝓝 (thermalLaw γ s k)) := by
    intro k
    apply (occupationLaw_tendsto m hγ h s k).congr'
    filter_upwards [hevent] with n hn
    simp only [p, if_pos hn]
  apply (CountableScheffe.discrete_scheffe p (thermalLaw γ s) hp
    (thermalLaw_nonneg hγ s) hpsum (thermalLaw_hasSum hγ s) hpoint).congr'
  filter_upwards [hevent] with n hn
  simp only [p, if_pos hn]

/-- Ambient-dimension formulation of the Werner--thermal occupation limit. -/
theorem werner_thermal_limit (D : ℕ) (hD : 2 ≤ D) (m : ℕ → ℕ)
    {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ ∑' k : Fin (D - 1) → ℕ,
      |WernerNormalization.occupationLaw n (m n) (D - 1) k -
        ∏ i, Thermal.geometric ((γ - 1) / γ) (k i)|) atTop (𝓝 0) :=
  occupationLaw_l1_tendsto m hγ h (D - 1) (by omega)

end Cloning.WernerAsymptotics
