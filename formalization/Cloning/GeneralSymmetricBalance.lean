import Cloning.GeneralSymmetricSplitting
import Cloning.WernerMultivariateConvolution

/-! # Exact multiplicity ratios and symmetric splitting balance

The squared physical splitting amplitudes reduce to products of ordinary
binomial coefficients. This is the finite combinatorial input for trace
preservation of the full Werner channel on arbitrary symmetric inputs.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix Kronecker

namespace Cloning.GeneralSymmetricOccupation

/-- Squared physical occupation-splitting amplitude. -/
def splittingWeight {n r d : ℕ} (p : Occupation n d) (q : Occupation r d) : ℝ :=
  (multiplicity p : ℝ) * multiplicity q / multiplicity (merge p q)

theorem splittingWeight_nonneg {n r d : ℕ} (p : Occupation n d) (q : Occupation r d) :
    0 ≤ splittingWeight p q := by unfold splittingWeight; positivity

/-- Exact multinomial-ratio identity for the actual occupation multiplicities. -/
theorem splittingWeight_binomial {n r d : ℕ} (p : Occupation n d) (q : Occupation r d) :
    splittingWeight p q =
      (∏ a : Fin d, ((q.val a + p.val a).choose (p.val a) : ℝ)) /
        ((n + r).choose n : ℝ) := by
  classical
  let P : ℝ := ∏ a : Fin d, (p.val a).factorial
  let Q : ℝ := ∏ a : Fin d, (q.val a).factorial
  let T : ℝ := ∏ a : Fin d, ((merge p q).val a).factorial
  let C : ℝ := ∏ a : Fin d, ((q.val a + p.val a).choose (p.val a) : ℝ)
  have hp : (multiplicity p : ℝ) * P = n.factorial := by
    dsimp [P]
    exact_mod_cast multiplicity_mul_factorials p
  have hq : (multiplicity q : ℝ) * Q = r.factorial := by
    dsimp [Q]
    exact_mod_cast multiplicity_mul_factorials q
  have ht : (multiplicity (merge p q) : ℝ) * T = (n + r).factorial := by
    dsimp [T]
    exact_mod_cast multiplicity_mul_factorials (merge p q)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a ha => by
    exact_mod_cast Nat.factorial_ne_zero (p.val a))
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a ha => by
    exact_mod_cast Nat.factorial_ne_zero (q.val a))
  have hprod : C * P * Q = T := by
    rw [show C * P * Q = ∏ a : Fin d,
      (((q.val a + p.val a).choose (p.val a) : ℝ) * (p.val a).factorial *
        (q.val a).factorial) by simp [C, P, Q, Finset.prod_mul_distrib]]
    apply Finset.prod_congr rfl
    intro a ha
    change ((q.val a + p.val a).choose (p.val a) : ℝ) * (p.val a).factorial *
      (q.val a).factorial = (p.val a + q.val a).factorial
    exact_mod_cast (by simpa [Nat.add_comm] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left (p.val a) (q.val a)))
  have hc : ((n + r).choose n : ℝ) * (n.factorial : ℝ) * r.factorial =
      (n + r).factorial := by
    exact_mod_cast (by simpa using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n r))
  have hm : (multiplicity (merge p q) : ℝ) ≠ 0 := by
    exact_mod_cast (multiplicity_pos (merge p q)).ne'
  have hchoose : ((n + r).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right n r)).ne'
  unfold splittingWeight
  apply (div_eq_div_iff hm hchoose).mpr
  apply (mul_right_cancel₀ (mul_ne_zero hP hQ))
  change ((multiplicity p : ℝ) * multiplicity q * ((n + r).choose n : ℝ)) * (P * Q) =
    (C * multiplicity (merge p q)) * (P * Q)
  calc
    _ = ((n + r).choose n : ℝ) * ((multiplicity p : ℝ) * P) *
        ((multiplicity q : ℝ) * Q) := by ring
    _ = (n + r).factorial := by rw [hp, hq, hc]
    _ = (multiplicity (merge p q) : ℝ) * T := ht.symm
    _ = _ := by rw [← hprod]; ring

/-- Entries of the environment partial trace of the splitting range projector. -/
theorem splitting_row_inner {n r d : ℕ} (p t : Occupation n d) (q : Occupation r d) :
    (∑ u : Occupation (n + r) d, splittingMatrix n r d (p, q) u *
      star (splittingMatrix n r d (t, q) u)) =
        if p = t then (splittingWeight p q : ℂ) else 0 := by
  classical
  rw [Finset.sum_eq_single (merge p q)]
  · simp only [splittingMatrix, ite_true]
    by_cases hpt : p = t
    · subst t
      simp only [ite_true, star_div₀, star_mul, Complex.star_def, Complex.conj_ofReal]
      have he : (Real.sqrt (multiplicity p : ℝ) * Real.sqrt (multiplicity q : ℝ) /
          Real.sqrt (multiplicity (merge p q) : ℝ)) *
          (Real.sqrt (multiplicity p : ℝ) * Real.sqrt (multiplicity q : ℝ) /
          Real.sqrt (multiplicity (merge p q) : ℝ)) = splittingWeight p q := by
        rw [← pow_two, div_pow, mul_pow, Real.sq_sqrt (by positivity),
          Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        rfl
      norm_cast
      convert he using 1
      ring
    · rw [if_neg hpt]
      have hm : merge p q ≠ merge t q := fun h => hpt (merge_left_injective q h)
      rw [if_neg hm]
      simp
  · intro u hu hn
    simp [splittingMatrix, hn]
  · simp

end Cloning.GeneralSymmetricOccupation

namespace Cloning.GeneralSymmetricOccupation

/-- Summing the physical splitting weights over every environment occupation
produces precisely the symmetric-dimension ratio. -/
theorem splittingWeight_sum {n r s : ℕ} (p : Occupation n (s + 1)) :
    (∑ q : Occupation r (s + 1), splittingWeight p q) =
      ((n + r + s).choose s : ℝ) / ((n + s).choose s : ℝ) := by
  classical
  simp_rw [splittingWeight_binomial]
  rw [← Finset.sum_div]
  have hsum : (∑ q : Occupation r (s + 1),
      ∏ a : Fin (s + 1), (q.val a + p.val a).choose (p.val a)) =
        (n + r + s).choose (n + s) := by
    calc
      _ = ∑ b ∈ Finset.Nat.antidiagonalTuple (s + 1) r,
          ∏ a, (b a + p.val a).choose (p.val a) := by
        apply Finset.sum_bij (fun q _ => q.val)
        · intro q hq
          exact Finset.Nat.mem_antidiagonalTuple.mpr (compositionEquiv r (s + 1) q).property
        · intro q hq t ht he
          exact Subtype.ext he
        · intro b hb
          refine ⟨(compositionEquiv r (s + 1)).symm
            ⟨b, Finset.Nat.mem_antidiagonalTuple.mp hb⟩, Finset.mem_univ _, ?_⟩
          rfl
        · intro q hq
          rfl
      _ = _ := by
        have hp : ∑ a, p.val a = n := (compositionEquiv n (s + 1) p).property
        rw [Cloning.Occupation.multivariate_choose_convolution, hp, Nat.add_comm r n]
  have hsumR : (∑ q : Occupation r (s + 1),
      ∏ a : Fin (s + 1), ((q.val a + p.val a).choose (p.val a) : ℝ)) =
        ((n + r + s).choose (n + s) : ℝ) := by exact_mod_cast hsum
  rw [hsumR, Cloning.Occupation.werner_balance_dimension_identity]

/-- The actual symmetric splitting matrix satisfies partial-trace balance;
there is no irreducibility or normalization premise. -/
theorem splittingMatrix_balance (n r s : ℕ) :
    Cloning.Compression.partialTrace
      (splittingMatrix n r (s + 1) * (splittingMatrix n r (s + 1)).conjTranspose) =
        (((n + r + s).choose s : ℝ) / ((n + s).choose s : ℝ)) •
          (1 : Matrix (Occupation n (s + 1)) (Occupation n (s + 1)) ℂ) := by
  classical
  ext p t
  simp only [Cloning.Compression.partialTrace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, splitting_row_inner, Matrix.smul_apply, Matrix.one_apply]
  by_cases hpt : p = t
  · simp only [if_pos hpt]
    rw [← Complex.ofReal_sum, splittingWeight_sum]
    simp
  · simp [hpt]

end Cloning.GeneralSymmetricOccupation
