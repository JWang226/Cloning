import Cloning.YoungDimensionRatio
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Second-order cancellation in Weyl dimension products

The finite-product estimate below separates the linear term from a genuinely
quadratic remainder. This is the analytic mechanism behind the cancellation
of centered row fluctuations in the flat-spectrum dimension ratio.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungDimensionRatio

/-- A direct finite-product Taylor estimate. No differentiability or
asymptotic expansion is assumed: the remainder bound follows by induction. -/
theorem product_quadratic_remainder {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, |x i| ≤ 1) :
    |(∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i| ≤
      (2 : ℝ) ^ S.card * (∑ i ∈ S, |x i|) ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hxa := hx a (Finset.mem_insert_self a S)
    have hxS : ∀ i ∈ S, |x i| ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hrest := ih hxS
    have hsum : |∑ i ∈ S, x i| ≤ ∑ i ∈ S, |x i| := Finset.abs_sum_le_sum_abs _ _
    have hsum0 : 0 ≤ ∑ i ∈ S, |x i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hcoef : 1 ≤ (2 : ℝ) ^ S.card := one_le_pow₀ (by norm_num)
    have hfac : |1 + x a| ≤ 2 := by
      calc
        _ ≤ |(1 : ℝ)| + |x a| := abs_add_le _ _
        _ ≤ 2 := by norm_num only [abs_one]; linarith
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      pow_succ]
    have halg : (1 + x a) * (∏ i ∈ S, (1 + x i)) - 1 - (x a + ∑ i ∈ S, x i) =
        (1 + x a) * ((∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i) +
          x a * (∑ i ∈ S, x i) := by ring
    rw [halg]
    calc
      _ ≤ |1 + x a| * |(∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i| +
          |x a| * |∑ i ∈ S, x i| := by
        simpa only [abs_mul] using abs_add_le
          ((1 + x a) * ((∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i))
          (x a * (∑ i ∈ S, x i))
      _ ≤ 2 * ((2 : ℝ) ^ S.card * (∑ i ∈ S, |x i|) ^ 2) +
          |x a| * (∑ i ∈ S, |x i|) := by
        exact add_le_add (mul_le_mul hfac hrest (abs_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hsum (abs_nonneg _))
      _ ≤ _ := by
        have hcross := mul_nonneg (show 0 ≤ 4 * (2 : ℝ) ^ S.card - 1 by linarith)
          (mul_nonneg (abs_nonneg (x a)) hsum0)
        have hsquare := mul_nonneg (le_trans zero_le_one hcoef) (sq_nonneg |x a|)
        nlinarith

/-- The quadratic remainder can be bounded by the Euclidean square sum. -/
theorem product_error_le_linear_add_square_sum {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ S, |x i| ≤ 1) :
    |(∏ i ∈ S, (1 + x i)) - 1| ≤
      |∑ i ∈ S, x i| + ((2 : ℝ) ^ S.card * S.card) * (∑ i ∈ S, (x i) ^ 2) := by
  have hrem := product_quadratic_remainder S x hx
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => |x i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hsplit : (∏ i ∈ S, (1 + x i)) - 1 =
      ((∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i) + (∑ i ∈ S, x i) := by ring
  rw [hsplit]
  calc
    _ ≤ |(∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i| + |∑ i ∈ S, x i| := abs_add_le _ _
    _ ≤ (2 : ℝ) ^ S.card * (∑ i ∈ S, |x i|) ^ 2 + |∑ i ∈ S, x i| :=
      add_le_add hrem le_rfl
    _ ≤ (2 : ℝ) ^ S.card * ((∑ i ∈ S, (x i) ^ 2) * S.card) + |∑ i ∈ S, x i| := by
      exact add_le_add (mul_le_mul_of_nonneg_left hcs
        (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) S.card)) le_rfl
    _ = _ := by ring

/-- Repeating a row quantity over all crossing roots multiplies its sum by
the number of columns beyond the rank boundary. -/
theorem sum_crossing_fst (r k : ℕ) (f : Fin r → ℝ) :
    (∑ a : Fin r × Fin k, f a.1) = (k : ℝ) * ∑ i, f i := by
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]

/-- The cancellation used below is proved from the total number of boxes. -/
theorem sum_centered_rows (r : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hboxes : ∑ i, row i = N) :
    (∑ i, (row i - N / (r : ℝ))) = 0 := by
  rw [Finset.sum_sub_distrib, hboxes]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  field_simp
  ring

/-- The sum of rescaled factor errors contains no centered row term. -/
theorem crossing_error_sum (r k : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hN : 0 < N) (hboxes : ∑ i, row i = N) :
    (∑ a : Fin r × Fin k, ((r : ℝ) * (row a.1 + crossingGap a) / N - 1)) =
      (r : ℝ) / N * ∑ a : Fin r × Fin k, crossingGap a := by
  have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  have heq (a : Fin r × Fin k) :
      (r : ℝ) * (row a.1 + crossingGap a) / N - 1 =
        (r : ℝ) / N * ((row a.1 - N / r) + crossingGap a) := by
    field_simp
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    sum_crossing_fst r k (fun i => row i - N / r),
    sum_centered_rows r row N hr hboxes]
  ring

theorem crossing_error_sum_bound (r k : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hN : 0 < N) (hboxes : ∑ i, row i = N) :
    |∑ a : Fin r × Fin k, ((r : ℝ) * (row a.1 + crossingGap a) / N - 1)| ≤
      (r : ℝ) * (r * k : ℕ) * ((r : ℝ) + k) / N := by
  rw [crossing_error_sum r k row N hr hN hboxes]
  have hg0 : 0 ≤ ∑ a : Fin r × Fin k, crossingGap a :=
    Finset.sum_nonneg (fun a _ => (crossingGap_pos a).le)
  rw [abs_of_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le) hg0)]
  have hg : (∑ a : Fin r × Fin k, crossingGap a) ≤
      (r * k : ℕ) * ((r : ℝ) + k) := by
    calc
      _ ≤ ∑ _a : Fin r × Fin k, ((r : ℝ) + k) :=
        Finset.sum_le_sum (fun a _ => crossingGap_le a)
      _ = _ := by simp [Fintype.card_prod]; ring
  calc
    _ ≤ (r : ℝ) / N * ((r * k : ℕ) * ((r : ℝ) + k)) :=
      mul_le_mul_of_nonneg_left hg (div_nonneg (Nat.cast_nonneg _) hN.le)
    _ = _ := by ring

/-- A bound on the second moment of all rescaled factors, in terms of the
actual squared row fluctuations. -/
theorem crossing_error_square_sum_bound (r k : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hN : 0 < N) :
    (∑ a : Fin r × Fin k, ((r : ℝ) * (row a.1 + crossingGap a) / N - 1) ^ 2) ≤
      2 * (r : ℝ) ^ 2 / N ^ 2 *
        ((k : ℝ) * (∑ i, (row i - N / r) ^ 2) +
          (r * k : ℕ) * ((r : ℝ) + k) ^ 2) := by
  have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  have hb (a : Fin r × Fin k) :
      ((r : ℝ) * (row a.1 + crossingGap a) / N - 1) ^ 2 ≤
        2 * (r : ℝ) ^ 2 / N ^ 2 *
          ((row a.1 - N / r) ^ 2 + ((r : ℝ) + k) ^ 2) := by
    have hg := crossingGap_le a
    have hg0 := (crossingGap_pos a).le
    have hd0 : 0 ≤ (r : ℝ) + k := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hg2 : crossingGap a ^ 2 ≤ ((r : ℝ) + k) ^ 2 :=
      sq_le_sq₀ hg0 hd0 |>.mpr hg
    have hab : ((row a.1 - N / r) + crossingGap a) ^ 2 ≤
        2 * ((row a.1 - N / r) ^ 2 + ((r : ℝ) + k) ^ 2) := by
      nlinarith [sq_nonneg ((row a.1 - N / r) - crossingGap a)]
    have heq : ((r : ℝ) * (row a.1 + crossingGap a) / N - 1) ^ 2 =
        ((r : ℝ) ^ 2 / N ^ 2) * ((row a.1 - N / r) + crossingGap a) ^ 2 := by
      field_simp
      ring
    rw [heq]
    calc
      _ ≤ ((r : ℝ) ^ 2 / N ^ 2) *
          (2 * ((row a.1 - N / r) ^ 2 + ((r : ℝ) + k) ^ 2)) :=
        mul_le_mul_of_nonneg_left hab (div_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ ∑ a : Fin r × Fin k, 2 * (r : ℝ) ^ 2 / N ^ 2 *
        ((row a.1 - N / r) ^ 2 + ((r : ℝ) + k) ^ 2) :=
      Finset.sum_le_sum (fun a _ => hb a)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        sum_crossing_fst r k (fun i => (row i - N / r) ^ 2)]
      simp [Fintype.card_prod]

/-- The manuscript's second-order expansion, with explicit uniform constants.
The only cancellation hypothesis is the actual box count `∑ row = N`.
The proximity assumptions only ensure that every factor error is at most one. -/
theorem dimensionRatio_second_order_error (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 0 < N) (hboxes : ∑ i, row i = N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ)
    (hsmall : (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N ≤ 1) :
    |dimensionRatio r k row / (leadingConstant r k * N ^ (r * k)) - 1| ≤
      (r : ℝ) * (r * k : ℕ) * ((r : ℝ) + k) / N +
      ((2 : ℝ) ^ (r * k) * (r * k : ℕ)) *
        (2 * (r : ℝ) ^ 2 / N ^ 2 *
          ((k : ℝ) * (∑ i, (row i - N / r) ^ 2) +
            (r * k : ℕ) * ((r : ℝ) + k) ^ 2)) := by
  let x : Fin r × Fin k → ℝ :=
    fun a => (r : ℝ) * (row a.1 + crossingGap a) / N - 1
  have hx : ∀ a ∈ Finset.univ, |x a| ≤ 1 := by
    intro a _
    exact (rescaled_factor_error r k row N δ hr hN hclose a).trans hsmall
  have hp := product_error_le_linear_add_square_sum Finset.univ x hx
  have hden : leadingConstant r k * N ^ (r * k) ≠ 0 :=
    (mul_pos (leadingConstant_pos r k hr) (pow_pos hN _)).ne'
  have hx1 (a : Fin r × Fin k) : 1 + x a =
      (r : ℝ) * (row a.1 + crossingGap a) / N := by dsimp [x]; ring
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hx1] at hp
  rw [dimensionRatio_factorization r k row N hr hN, mul_div_cancel_left₀ _ hden]
  exact hp.trans (add_le_add (crossing_error_sum_bound r k row N hr hN hboxes)
    (mul_le_mul_of_nonneg_left (crossing_error_square_sum_bound r k row N hr hN)
      (mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _))))

private theorem second_order_envelope_le (A B C V N : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hV : 0 ≤ V) (hN : 1 ≤ N) :
    A / N + B * V / N ^ 2 + C / N ^ 2 ≤
      (A + B + C) * (1 / N + V / N ^ 2) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hinv : 1 / N ^ 2 ≤ 1 / N := one_div_le_one_div_of_le hN0 hNN
  have hCdiv : C / N ^ 2 ≤ C / N := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv hC
  calc
    _ ≤ A / N + B * V / N ^ 2 + C / N := add_le_add le_rfl hCdiv
    _ = (A + C) * (1 / N) + B * (V / N ^ 2) := by ring
    _ ≤ (A + B + C) * (1 / N) + (A + B + C) * (V / N ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) (one_div_nonneg.mpr hN0.le))
        (mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hV (sq_nonneg _)))
    _ = _ := by ring

/-- An explicit constant depending only on rank and ambient dimension. -/
def secondOrderConstant (r k : ℕ) : ℝ :=
  (r : ℝ) * (r * k : ℕ) * ((r : ℝ) + k) +
    (2 : ℝ) ^ (r * k) * (r * k : ℕ) * 2 * (r : ℝ) ^ 2 * k +
    (2 : ℝ) ^ (r * k) * (r * k : ℕ) * 2 * (r : ℝ) ^ 2 *
      (r * k : ℕ) * ((r : ℝ) + k) ^ 2

theorem secondOrderConstant_nonneg (r k : ℕ) : 0 ≤ secondOrderConstant r k := by
  unfold secondOrderConstant
  positivity

/-- The precise manuscript rate `O(1/N + ‖u‖²/N²)`, as a uniform explicit
inequality. Here `uᵢ = rowᵢ - N/r` and the constant depends only on `r,k`.
No representation-dimension identification is asserted by this analytic result. -/
theorem dimensionRatio_second_order_rate (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 1 ≤ N) (hboxes : ∑ i, row i = N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ)
    (hsmall : (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N ≤ 1) :
    |dimensionRatio r k row / (leadingConstant r k * N ^ (r * k)) - 1| ≤
      secondOrderConstant r k *
        (1 / N + (∑ i, (row i - N / r) ^ 2) / N ^ 2) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbound := dimensionRatio_second_order_error r k row N δ hr hN0 hboxes hclose hsmall
  have henv := second_order_envelope_le
    ((r : ℝ) * (r * k : ℕ) * ((r : ℝ) + k))
    ((2 : ℝ) ^ (r * k) * (r * k : ℕ) * 2 * (r : ℝ) ^ 2 * k)
    ((2 : ℝ) ^ (r * k) * (r * k : ℕ) * 2 * (r : ℝ) ^ 2 *
      (r * k : ℕ) * ((r : ℝ) + k) ^ 2)
    (∑ i, (row i - N / r) ^ 2) N
    (by positivity) (by positivity) (by positivity)
    (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hN
  apply hbound.trans
  calc
    _ = (r : ℝ) * (r * k : ℕ) * ((r : ℝ) + k) / N +
        ((2 : ℝ) ^ (r * k) * (r * k : ℕ) * 2 * (r : ℝ) ^ 2 * k) *
          (∑ i, (row i - N / r) ^ 2) / N ^ 2 +
        ((2 : ℝ) ^ (r * k) * (r * k : ℕ) * 2 * (r : ℝ) ^ 2 *
          (r * k : ℕ) * ((r : ℝ) + k) ^ 2) / N ^ 2 := by ring
    _ ≤ _ := henv

/-- The same estimate in Landau notation. The small-factor condition is now
derived, rather than assumed, from convergence of the actual row proportions. -/
theorem dimensionRatio_second_order_isBigO (r k : ℕ) (hr : 0 < r)
    (row : ℕ → Fin r → ℝ) (N δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hδ : Tendsto δ atTop (𝓝 0))
    (hboxes : ∀ n, ∑ i, row n i = N n)
    (hclose : ∀ n i, |row n i / N n - 1 / (r : ℝ)| ≤ δ n) :
    Asymptotics.IsBigO atTop
      (fun n => dimensionRatio r k (row n) /
        (leadingConstant r k * (N n) ^ (r * k)) - 1)
      (fun n => 1 / N n + (∑ i, (row n i - N n / r) ^ 2) / (N n) ^ 2) := by
  have hinv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hN
  have harg : Tendsto
      (fun n => (r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (((tendsto_const_nhds (x := (r : ℝ))).mul hδ).add
        ((tendsto_const_nhds (x := (r : ℝ) * ((r : ℝ) + k))).mul hinv))
  have hsmall : ∀ᶠ n in atTop,
      (r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n < 1 :=
    harg.eventually (eventually_lt_nhds zero_lt_one)
  have hNlarge : ∀ᶠ n in atTop, 1 ≤ N n := hN.eventually (eventually_ge_atTop 1)
  apply Asymptotics.IsBigO.of_bound (secondOrderConstant r k)
  filter_upwards [hNlarge, hsmall] with n hn hs
  have hrate := dimensionRatio_second_order_rate r k (row n) (N n) (δ n)
    hr hn (hboxes n) (hclose n) hs.le
  have hnonneg : 0 ≤ 1 / N n + (∑ i, (row n i - N n / r) ^ 2) / (N n) ^ 2 :=
    add_nonneg (one_div_nonneg.mpr (le_trans zero_le_one hn))
      (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hrate

end Cloning.YoungDimensionRatio
