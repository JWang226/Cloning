import Cloning.WeylNumberTaylor

/-! Analytic-vector bounds for the literal finite-support Fock ladder. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem numberIterate_succ_right (a : Fin d → ℂ) (c : NumberCoefficients d) (m : ℕ) :
    numberIterate a c (m+1) = numberIterate a (numberGenerator a c) m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (numberGenerator a) ih

theorem numberIterate_add (a : Fin d → ℂ) (c e : NumberCoefficients d) (m : ℕ) :
    numberIterate a (c+e) m = numberIterate a c m + numberIterate a e m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [numberIterate_succ, ih, map_add]

theorem numberIterate_sub (a : Fin d → ℂ) (c e : NumberCoefficients d) (m : ℕ) :
    numberIterate a (c-e) m = numberIterate a c m - numberIterate a e m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [numberIterate_succ, ih, map_sub]

theorem numberIterate_smul (a : Fin d → ℂ) (z : ℂ) (c : NumberCoefficients d) (m : ℕ) :
    numberIterate a (z • c) m = z • numberIterate a c m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [numberIterate_succ, ih, map_smul]

theorem numberIterate_sum {ι : Type*} (a : Fin d → ℂ)
    (s : Finset ι) (c : ι → NumberCoefficients d) (m : ℕ) :
    numberIterate a (∑ i ∈ s, c i) m = ∑ i ∈ s, numberIterate a (c i) m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [numberIterate_succ, ih, map_sum]

def numberPower (a : Fin d → ℂ) (k : Fin d → ℕ) (m : ℕ) : Fock d :=
  numberVector (numberIterate a (Finsupp.single k 1) m)

@[simp] theorem numberPower_zero (a : Fin d → ℂ) (k : Fin d → ℕ) :
    numberPower a k 0 = numberBasis d k := by simp [numberPower]

theorem numberPower_succ (a : Fin d → ℂ) (k : Fin d → ℕ) (m : ℕ) :
    numberPower a k (m+1) =
      ∑ i, ((a i * (Real.sqrt (k i+1 : ℝ) : ℂ)) •
          numberPower a (Function.update k i (k i+1)) m -
        (starRingEnd ℂ (a i) * (Real.sqrt (k i : ℝ) : ℂ)) •
          numberPower a (Function.update k i (k i-1)) m) := by
  unfold numberPower
  rw [numberIterate_succ_right, numberGenerator_single, one_smul]
  simp only [numberLadderCoefficients, numberIterate_sum, numberIterate_sub, map_sum, map_sub]
  apply Finset.sum_congr rfl
  intro i _
  have hs (l : Fin d → ℕ) (c : ℂ) :
      Finsupp.single l c = c • Finsupp.single l (1 : ℂ) := by simp
  rw [hs _ (a i * _), hs _ (starRingEnd ℂ (a i) * _)]
  simp only [numberIterate_smul, map_smul]

/-- Each application raises every occupation coordinate by at most one. The
finite ladder tree therefore has a square-root, rather than linear, growth
factor per step. The bound is uniform in a sum-norm amplitude ball. -/
theorem numberPower_norm_le (a : Fin d → ℂ) (m K : ℕ) (k : Fin d → ℕ)
    (hk : ∀ i, k i ≤ K) :
    ‖numberPower a k m‖ ≤ (2 * (∑ i, ‖a i‖) * Real.sqrt (K+m : ℝ)) ^ m := by
  induction m generalizing K k with
  | zero => simp [numberPower_zero, (numberBasis d).orthonormal.norm_eq_one]
  | succ m ih =>
    let C : ℝ := 2 * (∑ i, ‖a i‖) * Real.sqrt (K+(m+1) : ℝ)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hup (i : Fin d) :
        ‖numberPower a (Function.update k i (k i+1)) m‖ ≤ C ^ m := by
      have h := ih (K+1) (Function.update k i (k i+1)) (by
        intro j
        by_cases hji : j = i
        · subst j; simp only [Function.update_self]; have := hk i; omega
        · rw [Function.update_of_ne hji]; exact (hk j).trans (Nat.le_succ K))
      simpa only [C, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using h
    have hdown (i : Fin d) :
        ‖numberPower a (Function.update k i (k i-1)) m‖ ≤ C ^ m := by
      have h := ih (K+1) (Function.update k i (k i-1)) (by
        intro j
        by_cases hji : j = i
        · subst j; simp only [Function.update_self]; have := hk i; omega
        · rw [Function.update_of_ne hji]; exact (hk j).trans (Nat.le_succ K))
      simpa only [C, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using h
    have hp (i : Fin d) : ‖a i * (Real.sqrt (k i+1 : ℝ) : ℂ)‖ ≤
        ‖a i‖ * Real.sqrt (K+(m+1) : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast
        (show k i+1 ≤ K+(m+1) by have := hk i; omega))) (norm_nonneg _)
    have hm (i : Fin d) : ‖starRingEnd ℂ (a i) * (Real.sqrt (k i : ℝ) : ℂ)‖ ≤
        ‖a i‖ * Real.sqrt (K+(m+1) : ℝ) := by
      rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast
        (show k i ≤ K+(m+1) by have := hk i; omega))) (norm_nonneg _)
    rw [numberPower_succ]
    calc
      _ ≤ ∑ i, (‖(a i * (Real.sqrt (k i+1 : ℝ) : ℂ)) •
            numberPower a (Function.update k i (k i+1)) m‖ +
          ‖(starRingEnd ℂ (a i) * (Real.sqrt (k i : ℝ) : ℂ)) •
            numberPower a (Function.update k i (k i-1)) m‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sub_le _ _)
      _ ≤ ∑ i, (‖a i‖ * Real.sqrt (K+(m+1) : ℝ) * C^m +
          ‖a i‖ * Real.sqrt (K+(m+1) : ℝ) * C^m) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [norm_smul]
        exact add_le_add
          (mul_le_mul (hp i) (hup i) (norm_nonneg _) (by positivity))
          (mul_le_mul (hm i) (hdown i) (norm_nonneg _) (by positivity))
      _ = C^(m+1) := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
        dsimp [C]
        rw [pow_succ]
        ring
      _ = _ := by simp only [C, Nat.cast_add, Nat.cast_one]

end Cloning.MultimodeCoherent
