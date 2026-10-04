import Cloning.YoungTwoRowMoment
import Cloning.YoungDimensionSecondOrder

/-!
# Forward Weyl-product moment for the concrete two-row Young law

A global finite-product remainder bound replaces the small-factor hypothesis
in the local Taylor estimate. Normalized factors are uniformly bounded because
the actual row lengths lie between zero and the number of boxes. The proved
second moment of the concrete two-row law therefore yields the forward
dimension-ratio expectation with error `O(1/N)`, without a concentration or
moment premise. Representation-space dimension identification remains separate.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungTwoRow
open YoungDimensionRatio

/-- A second-order finite-product bound with uniformly bounded factors.
The errors themselves need not tend to zero uniformly. -/
theorem bounded_product_quadratic_remainder {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (B : ℝ) (hB : 1 ≤ B) (hx : ∀ i ∈ S, |1 + x i| ≤ B) :
    |(∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i| ≤
      B ^ S.card * (∑ i ∈ S, |x i|) ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hxa := hx a (Finset.mem_insert_self a S)
    have hrest := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hsum : |∑ i ∈ S, x i| ≤ ∑ i ∈ S, |x i| := Finset.abs_sum_le_sum_abs _ _
    have hsum0 : 0 ≤ ∑ i ∈ S, |x i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hcoef : 1 ≤ B ^ S.card * B := by
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) hB
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
      _ ≤ B * (B ^ S.card * (∑ i ∈ S, |x i|) ^ 2) +
          |x a| * (∑ i ∈ S, |x i|) :=
        add_le_add (mul_le_mul hxa hrest (abs_nonneg _) (le_trans zero_le_one hB))
          (mul_le_mul_of_nonneg_left hsum (abs_nonneg _))
      _ ≤ _ := by
        have hcross := mul_nonneg (show 0 ≤ 2 * (B ^ S.card * B) - 1 by linarith)
          (mul_nonneg (abs_nonneg (x a)) hsum0)
        have hsquare := mul_nonneg (le_trans zero_le_one hcoef) (sq_nonneg |x a|)
        nlinarith

theorem bounded_product_error {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (B : ℝ) (hB : 1 ≤ B) (hx : ∀ i ∈ S, |1 + x i| ≤ B) :
    |(∏ i ∈ S, (1 + x i)) - 1| ≤
      |∑ i ∈ S, x i| + (B ^ S.card * S.card) * (∑ i ∈ S, (x i) ^ 2) := by
  have hrem := bounded_product_quadratic_remainder S x B hB hx
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => |x i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hsplit : (∏ i ∈ S, (1 + x i)) - 1 =
      ((∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i) + ∑ i ∈ S, x i := by ring
  rw [hsplit]
  calc
    _ ≤ |(∏ i ∈ S, (1 + x i)) - 1 - ∑ i ∈ S, x i| + |∑ i ∈ S, x i| := abs_add_le _ _
    _ ≤ B ^ S.card * (∑ i ∈ S, |x i|) ^ 2 + |∑ i ∈ S, x i| := add_le_add hrem le_rfl
    _ ≤ B ^ S.card * ((∑ i ∈ S, (x i) ^ 2) * S.card) + |∑ i ∈ S, x i| :=
      add_le_add (mul_le_mul_of_nonneg_left hcs (pow_nonneg (le_trans zero_le_one hB) _)) le_rfl
    _ = _ := by ring

/-- The actual two integer row lengths viewed as a real row vector. -/
def rowVector (N : ℕ) (p : Path N) (i : Fin 2) : ℝ :=
  if i.val = 0 then upperRow N p else lowerRow N p

theorem rowVector_sum (N : ℕ) (p : Path N) : (∑ i, rowVector N p i) = N := by
  simpa [rowVector, Fin.sum_univ_two] using congrArg (fun n : ℕ => (n : ℝ)) (row_sum N p)

theorem rowVector_bounds (N : ℕ) (p : Path N) (i : Fin 2) :
    0 ≤ rowVector N p i ∧ rowVector N p i ≤ N := by
  have h := row_sum N p
  have ht : upperRow N p ≤ N := by omega
  have hb : lowerRow N p ≤ N := by omega
  dsimp [rowVector]
  split_ifs
  · exact ⟨Nat.cast_nonneg _, by exact_mod_cast ht⟩
  · exact ⟨Nat.cast_nonneg _, by exact_mod_cast hb⟩

theorem rowVector_variance (N : ℕ) (p : Path N) :
    (∑ i, (rowVector N p i - (N : ℝ) / 2) ^ 2) = rowVariance N p := by
  simp [rowVector, rowVariance, Fin.sum_univ_two]

/-- A global bound on normalized crossing factors for every actual row shape. -/
theorem row_factor_bound (k N : ℕ) (hN : 1 ≤ N) (p : Path N)
    (a : Fin 2 × Fin k) :
    |2 * (rowVector N p a.1 + crossingGap a) / N| ≤ 2 + 2 * (2 + (k : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hrow := rowVector_bounds N p a.1
  have hgap := crossingGap_le a
  have hgap0 := (crossingGap_pos a).le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (add_nonneg hrow.1 hgap0)) hN0.le)]
  apply (div_le_iff₀ hN0).mpr
  norm_num only [Nat.cast_ofNat] at hgap
  nlinarith [mul_nonneg (show 0 ≤ 2 + (k : ℝ) by linarith) (sub_nonneg.mpr hN1)]

/-- The Taylor bound is global over this concrete law; no typical set is needed. -/
theorem dimensionRatio_global_error (k N : ℕ) (hN : 1 ≤ N) (p : Path N) :
    |dimensionRatio 2 k (rowVector N p) /
      (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1| ≤
      2 * (2 * k : ℕ) * (2 + (k : ℝ)) / N +
        ((2 + 2 * (2 + (k : ℝ))) ^ (2 * k) * (2 * k : ℕ)) *
          (8 / (N : ℝ) ^ 2 * ((k : ℝ) * rowVariance N p +
            (2 * k : ℕ) * (2 + (k : ℝ)) ^ 2)) := by
  let x : Fin 2 × Fin k → ℝ :=
    fun a => 2 * (rowVector N p a.1 + crossingGap a) / N - 1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hB : (1 : ℝ) ≤ 2 + 2 * (2 + (k : ℝ)) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hx1 (a : Fin 2 × Fin k) : 1 + x a =
      2 * (rowVector N p a.1 + crossingGap a) / N := by dsimp [x]; ring
  have hp := bounded_product_error Finset.univ x (2 + 2 * (2 + (k : ℝ))) hB
    (fun a _ => by rw [hx1]; exact row_factor_bound k N hN p a)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hx1] at hp
  have hden : leadingConstant 2 k * (N : ℝ) ^ (2 * k) ≠ 0 :=
    (mul_pos (leadingConstant_pos 2 k (by decide)) (pow_pos hN0 _)).ne'
  rw [dimensionRatio_factorization 2 k (rowVector N p) N (by decide) hN0,
    mul_div_cancel_left₀ _ hden]
  have hlin := crossing_error_sum_bound 2 k (rowVector N p) N (by decide) hN0
    (rowVector_sum N p)
  have hquad := crossing_error_square_sum_bound 2 k (rowVector N p) N (by decide) hN0
  norm_num only [Nat.cast_ofNat] at hlin hquad ⊢
  rw [rowVector_variance] at hquad
  have h := hp.trans (add_le_add hlin (mul_le_mul_of_nonneg_left hquad
    (mul_nonneg (pow_nonneg (by positivity) _) (Nat.cast_nonneg _))))
  norm_num only [Nat.reducePow, mul_one, Nat.cast_ofNat] at h
  convert h using 1

/-- An explicit error constant depending only on the ambient codimension. -/
def dimensionMomentConstant (k : ℕ) : ℝ :=
  2 * (2 * k : ℕ) * (2 + (k : ℝ)) +
    ((2 + 2 * (2 + (k : ℝ))) ^ (2 * k) * (2 * k : ℕ)) * 8 *
      (3 * (k : ℝ) / 2 + (2 * k : ℕ) * (2 + (k : ℝ)) ^ 2)

theorem dimensionMomentConstant_nonneg (k : ℕ) : 0 ≤ dimensionMomentConstant k := by
  unfold dimensionMomentConstant
  positivity

/-- The whole concrete law, including its extreme shapes, satisfies a
mean absolute relative-error estimate of order `1/N`. -/
theorem mean_absolute_dimensionRatio_error (k N : ℕ) (hN : 1 ≤ N) :
    (∑ p : Path N, weight N p * |dimensionRatio 2 k (rowVector N p) /
      (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1|) ≤
      dimensionMomentConstant k / N := by
  let L : ℝ := 2 * (2 * k : ℕ) * (2 + (k : ℝ))
  let Q : ℝ := (2 + 2 * (2 + (k : ℝ))) ^ (2 * k) * (2 * k : ℕ)
  let D : ℝ := (2 * k : ℕ) * (2 + (k : ℝ)) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hquad : 0 ≤ Q * 8 / (N : ℝ) ^ 2 * k := by positivity
  have hmean :
      (∑ p : Path N, weight N p *
        (L / N + Q * (8 / (N : ℝ) ^ 2 * ((k : ℝ) * rowVariance N p + D)))) ≤
      L / N + Q * 8 / (N : ℝ) ^ 2 * D +
        (Q * 8 / (N : ℝ) ^ 2 * k) * (3 * (N : ℝ) / 2) := by
    calc
      _ = (L / N + Q * 8 / (N : ℝ) ^ 2 * D) * (∑ p : Path N, weight N p) +
          (Q * 8 / (N : ℝ) ^ 2 * k) * (∑ p : Path N, weight N p * rowVariance N p) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ _ := by
        rw [weight_sum, mul_one]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (centered_second_moment_le N) hquad)
  have hinv : 1 / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hN0 (by nlinarith)
  have htail : Q * 8 * D / (N : ℝ) ^ 2 ≤ Q * 8 * D / N := by
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hinv (mul_nonneg (mul_nonneg hQ (by norm_num)) hD)
  calc
    _ ≤ ∑ p : Path N, weight N p *
        (L / N + Q * (8 / (N : ℝ) ^ 2 * ((k : ℝ) * rowVariance N p + D))) :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
        (dimensionRatio_global_error k N hN p) (weight_nonneg N p))
    _ ≤ L / N + Q * 8 / (N : ℝ) ^ 2 * D +
        (Q * 8 / (N : ℝ) ^ 2 * k) * (3 * (N : ℝ) / 2) := hmean
    _ = (L + Q * 8 * (3 * (k : ℝ) / 2)) / N + Q * 8 * D / (N : ℝ) ^ 2 := by
      field_simp
      ring
    _ ≤ (L + Q * 8 * (3 * (k : ℝ) / 2)) / N + Q * 8 * D / N :=
      add_le_add le_rfl htail
    _ = dimensionMomentConstant k / N := by unfold dimensionMomentConstant; dsimp [L, Q, D]; ring

/-- The actual expected crossing-root dimension ratio of the two-row law. -/
def meanDimensionRatio (k N : ℕ) : ℝ :=
  ∑ p : Path N, weight N p * dimensionRatio 2 k (rowVector N p)

/-- The manuscript's forward dimension-ratio moment, with an explicit constant
and with the law and its second moment already proved rather than assumed. -/
theorem meanDimensionRatio_relative_error (k N : ℕ) (hN : 1 ≤ N) :
    |meanDimensionRatio k N /
      (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1| ≤
      dimensionMomentConstant k / N := by
  have heq : meanDimensionRatio k N /
      (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1 =
      ∑ p : Path N, weight N p * (dimensionRatio 2 k (rowVector N p) /
        (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, weight_sum,
      div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul, meanDimensionRatio]
  rw [heq]
  calc
    _ ≤ ∑ p : Path N, |weight N p * (dimensionRatio 2 k (rowVector N p) /
        (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : Path N, weight N p * |dimensionRatio 2 k (rowVector N p) /
        (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1| := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_of_nonneg (weight_nonneg N p)]
    _ ≤ _ := mean_absolute_dimensionRatio_error k N hN

/-- The integer two-row shape reconstructed from its size and row gap. -/
def shapeRowVector (N s : ℕ) (i : Fin 2) : ℝ :=
  if i.val = 0 then ((N + s) / 2 : ℕ) else ((N - s) / 2 : ℕ)

theorem rowVector_eq_shapeRowVector (N : ℕ) (p : Path N) (hp : legal N p) :
    rowVector N p = shapeRowVector N (spin N p) := by
  funext i
  simp only [rowVector, shapeRowVector, upperRow_eq_of_legal N p hp,
    lowerRow_eq_of_legal N p hp]

/-- The path expectation is exactly the expectation under the explicit shape
law `(gap+1) * tableauPathCount / 2^N`. -/
theorem meanDimensionRatio_eq_shape_sum (k N : ℕ) :
    meanDimensionRatio k N = ∑ s : Fin (N + 1), shapeProbability N s *
      dimensionRatio 2 k (shapeRowVector N s) := by
  rw [shape_expectation N (fun s => dimensionRatio 2 k (shapeRowVector N s))]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hl : legal N p
  · rw [rowVector_eq_shapeRowVector N p hl]
  · rw [weight_eq_zero_of_not_legal N p hl]
    simp

/-- The forward moment bound expressed directly for the concrete shape law. -/
theorem shape_dimensionRatio_relative_error (k N : ℕ) (hN : 1 ≤ N) :
    |(∑ s : Fin (N + 1), shapeProbability N s * dimensionRatio 2 k (shapeRowVector N s)) /
      (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1| ≤ dimensionMomentConstant k / N := by
  rw [← meanDimensionRatio_eq_shape_sum]
  exact meanDimensionRatio_relative_error k N hN

/-- The explicit `O(1/N)` rate for the actual forward dimension-ratio moment. -/
theorem meanDimensionRatio_relative_isBigO (k : ℕ) :
    Asymptotics.IsBigO atTop
      (fun N : ℕ => meanDimensionRatio k N /
        (leadingConstant 2 k * (N : ℝ) ^ (2 * k)) - 1)
      (fun N : ℕ => 1 / (N : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (dimensionMomentConstant k)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h := meanDimensionRatio_relative_error k N hN
  have hn : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
    mul_one_div] using h

end Cloning.YoungTwoRow
