import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar part of the finite projector converse

The manuscript's operator step produces nonnegative output block traces `z`,
whose total is the input dimension-ratio moment. This file proves the ensuing
finite Cauchy--Schwarz bound, including the exact scalar calculation of a
support-block fidelity and the trace inflation. It does **not** identify an
arbitrary quantum channel with this scalar data: covariance, Schur--Weyl
decomposition, and operator monotonicity of fidelity remain external steps.

All results below are proved, without added axioms or `sorry`.
-/

open scoped BigOperators

namespace Cloning.Projector

/-- The trace of a block after replacing its rank-`s` support by the ambient
identity of dimension `d`. The multiplicity-space dimension cancels. -/
theorem inflated_block_trace (p d s k : ℝ) (hs : s ≠ 0) (hk : k ≠ 0) :
    (d * k) * (p / (s * k)) = p * (d / s) := by
  field_simp

/-- Exact root fidelity of one flat block, computed by summing its identical
nonzero diagonal contributions. Here `d` is the ambient irrep dimension, `s`
is the support rank, and `k` is the multiplicity-space dimension. -/
theorem flat_block_root_fidelity (z q d s k : ℝ)
    (hz : 0 ≤ z) (hq : 0 ≤ q) (hd : 0 < d) (hs : 0 < s) (hk : 0 < k) :
    (s * k) * Real.sqrt ((z / (d * k)) * (q / (s * k))) =
      Real.sqrt (z * q / (d / s)) := by
  have hrad : 0 ≤ (z / (d * k)) * (q / (s * k)) := by positivity
  have hsq : ((s * k) * Real.sqrt ((z / (d * k)) * (q / (s * k)))) ^ 2 =
      z * q / (d / s) := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp
  have hnonneg : 0 ≤ (s * k) * Real.sqrt ((z / (d * k)) * (q / (s * k))) := by
    positivity
  rw [← hsq, Real.sqrt_sq hnonneg]

/-- Finite Cauchy--Schwarz in exactly the scalar form used by the converse. -/
theorem block_fidelity_sq_le {ι : Type*} (S : Finset ι)
    (z q R : ι → ℝ)
    (hz : ∀ i ∈ S, 0 ≤ z i) (hq : ∀ i ∈ S, 0 ≤ q i)
    (hR : ∀ i ∈ S, 0 < R i) :
    (∑ i ∈ S, Real.sqrt (z i * q i / R i)) ^ 2 ≤
      (∑ i ∈ S, z i) * (∑ i ∈ S, q i / R i) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S hz
      (fun i hi => div_nonneg (hq i hi) (hR i hi).le)
  intro i hi
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (hz i hi) (hq i hi)) (hR i hi).le)]
  ring

/-- The block traces may have mass outside the target support. Only an upper
bound on the mass of supported output blocks is needed. -/
theorem block_fidelity_le_of_mass_le {ι : Type*} (S : Finset ι)
    (z q R : ι → ℝ) (A : ℝ)
    (hz : ∀ i ∈ S, 0 ≤ z i) (hq : ∀ i ∈ S, 0 ≤ q i)
    (hR : ∀ i ∈ S, 0 < R i) (hmass : ∑ i ∈ S, z i ≤ A) :
    (∑ i ∈ S, Real.sqrt (z i * q i / R i)) ≤
      Real.sqrt (A * (∑ i ∈ S, q i / R i)) := by
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ (∑ i ∈ S, z i) * (∑ i ∈ S, q i / R i) :=
      block_fidelity_sq_le S z q R hz hq hR
    _ ≤ A * (∑ i ∈ S, q i / R i) := by
      apply mul_le_mul_of_nonneg_right hmass
      exact Finset.sum_nonneg (fun i hi => div_nonneg (hq i hi) (hR i hi).le)

/-- The finite projector-converse bound after the operator reduction. The
hypothesis `hdom` explicitly records the unformalized fidelity domination. -/
theorem finite_projector_converse_of_reduction {ι κ : Type*}
    (I : Finset ι) (O : Finset κ) (p Rin : ι → ℝ) (z q Rout : κ → ℝ)
    (F : ℝ)
    (hz : ∀ i ∈ O, 0 ≤ z i) (hq : ∀ i ∈ O, 0 ≤ q i)
    (hR : ∀ i ∈ O, 0 < Rout i)
    (hmass : ∑ i ∈ O, z i ≤ ∑ j ∈ I, p j * Rin j)
    (hdom : F ≤ ∑ i ∈ O, Real.sqrt (z i * q i / Rout i)) :
    F ≤ Real.sqrt ((∑ j ∈ I, p j * Rin j) * (∑ i ∈ O, q i / Rout i)) :=
  hdom.trans (block_fidelity_le_of_mass_le O z q Rout _ hz hq hR hmass)

/-- Trace preservation on all output blocks implies the supported mass bound. -/
theorem supported_mass_le {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (z : ι → ℝ) (A : ℝ)
    (hST : S ⊆ T) (hz : ∀ i ∈ T, 0 ≤ z i) (htotal : ∑ i ∈ T, z i = A) :
    ∑ i ∈ S, z i ≤ A := by
  rw [← htotal]
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ => hz i hi)

/-- The direct-sum trace inflation is the input dimension-ratio moment. -/
theorem inflated_trace_eq_moment {ι : Type*} (I : Finset ι)
    (p d s k : ι → ℝ) (hs : ∀ i ∈ I, s i ≠ 0) (hk : ∀ i ∈ I, k i ≠ 0) :
    (∑ i ∈ I, (d i * k i) * (p i / (s i * k i))) =
      ∑ i ∈ I, p i * (d i / s i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact inflated_block_trace _ _ _ _ (hs i hi) (hk i hi)

/-- Each cross-root factor in the Weyl dimension ratio lies between `1`
and `N + 1` if the row length lies in `[0,N]` and the root gap is at least `1`.
The application has `δ = j - i` and `x = λᵢ`. -/
theorem dimension_factor_bounds (x N δ : ℝ)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hδ : 1 ≤ δ) :
    1 ≤ (x + δ) / δ ∧ (x + δ) / δ ≤ N + 1 := by
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  have hN : 0 ≤ N := hx.trans hxN
  constructor
  · apply (le_div_iff₀ hδpos).2
    linarith
  · apply (div_le_iff₀ hδpos).2
    nlinarith [mul_le_mul_of_nonneg_left hδ hN]

/-- The global polynomial bound on the dimension ratio, as a product over
the crossing positive roots. For the rank-`r` model `S.card = r * (d-r)`. -/
theorem dimension_ratio_bounds {ι : Type*} (S : Finset ι)
    (x δ : ι → ℝ) (N : ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hxN : ∀ i ∈ S, x i ≤ N)
    (hδ : ∀ i ∈ S, 1 ≤ δ i) :
    1 ≤ (∏ i ∈ S, (x i + δ i) / δ i) ∧
      (∏ i ∈ S, (x i + δ i) / δ i) ≤ (N + 1) ^ S.card := by
  have hbounds := fun i hi => dimension_factor_bounds (x i) N (δ i)
    (hx i hi) (hxN i hi) (hδ i hi)
  constructor
  · exact Finset.one_le_prod (fun i hi => (hbounds i hi).1)
  · calc
      _ ≤ ∏ _i ∈ S, (N + 1) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact zero_le_one.trans (hbounds i hi).1
        · intro i hi
          exact (hbounds i hi).2
      _ = (N + 1) ^ S.card := by simp

/-- The scalar Cauchy--Schwarz bound is sharp: distributing available mass
in proportion to `b` saturates it. This does not assert that the optimizing
mass allocation can be realized by a quantum channel. -/
theorem scalar_bound_is_sharp {ι : Type*} (S : Finset ι)
    (b : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hB : 0 < ∑ i ∈ S, b i) :
    (∑ i ∈ S, A * b i / (∑ j ∈ S, b j)) = A ∧
    (∑ i ∈ S, Real.sqrt ((A * b i / (∑ j ∈ S, b j)) * b i)) =
      Real.sqrt (A * (∑ i ∈ S, b i)) := by
  let B := ∑ i ∈ S, b i
  have hB' : 0 < B := hB
  constructor
  · simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    change A * B * B⁻¹ = A
    rw [mul_assoc, mul_inv_cancel₀ hB'.ne', mul_one]
  · have hterm : ∀ i ∈ S,
        Real.sqrt ((A * b i / B) * b i) = Real.sqrt (A / B) * b i := by
      intro i hi
      have heq : (A * b i / B) * b i = (A / B) * (b i) ^ 2 := by ring
      rw [heq, Real.sqrt_mul (div_nonneg hA hB'.le), Real.sqrt_sq (hb i hi)]
    change (∑ i ∈ S, Real.sqrt ((A * b i / B) * b i)) = Real.sqrt (A * B)
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    change Real.sqrt (A / B) * B = Real.sqrt (A * B)
    have heq : A * B = (A / B) * B ^ 2 := by field_simp
    rw [heq, Real.sqrt_mul (div_nonneg hA hB'.le), Real.sqrt_sq hB'.le]

/-- Expansion of the centered row-length square sum. -/
theorem centered_square_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ) (c : ℝ) :
    (∑ i ∈ S, (x i - c) ^ 2) =
      (∑ i ∈ S, (x i) ^ 2) - 2 * c * (∑ i ∈ S, x i) + S.card * c ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- If the row lengths sum to `N`, centering them at `N/r` removes
exactly `N²/r` from their square sum. -/
theorem centered_square_sum_eq {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (N r : ℝ) (hr : r ≠ 0) (hcard : (S.card : ℝ) = r)
    (hsum : ∑ i ∈ S, x i = N) :
    (∑ i ∈ S, (x i - N / r) ^ 2) = (∑ i ∈ S, (x i) ^ 2) - N ^ 2 / r := by
  rw [centered_square_sum, hsum, hcard]
  field_simp
  ring

/-- Ordered row lengths make every positive-root gap nonnegative. -/
theorem root_gap_sum_nonneg {ι : Type*} (S : Finset (ι × ι)) (x : ι → ℝ)
    (horder : ∀ ij ∈ S, x ij.2 ≤ x ij.1) :
    0 ≤ ∑ ij ∈ S, (x ij.1 - x ij.2) :=
  Finset.sum_nonneg (fun ij hij => sub_nonneg.mpr (horder ij hij))

/-- The sum over positive roots equals the linear term in the `U(r)`
quadratic Casimir. Row indices here start at zero. -/
theorem root_gap_sum_eq_linear (r : ℕ) (x : Fin r → ℝ) :
    (∑ i, ∑ j ∈ Finset.Ioi i, (x i - x j)) =
      ∑ i, x i * ((r : ℝ) - 1 - 2 * (i : ℕ)) := by
  classical
  have hIoi (i : Fin r) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    ext j
    simp
  have hIio (i : Fin r) : Finset.Iio i = Finset.univ.filter (fun j => j < i) := by
    ext j
    simp
  have hswap : (∑ i, ∑ j ∈ Finset.Ioi i, x j) =
      ∑ j, ∑ _i ∈ Finset.Iio j, x j := by
    simp_rw [hIoi, hIio, Finset.sum_filter]
    rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib]
  rw [hswap, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi, Fin.card_Iio]
  have hir : (i : ℕ) ≤ r - 1 := Nat.le_sub_one_of_lt i.isLt
  have hr : 1 ≤ r := Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  rw [Nat.cast_sub hir, Nat.cast_sub hr]
  ring

/-- Exact algebraic identity for the Casimir eigenvalue in the manuscript.
The representation-theoretic assertion that this polynomial *is* the
Casimir eigenvalue is not required or asserted here. -/
theorem casimir_polynomial_eq_centered (r : ℕ) (x : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hsum : ∑ i, x i = N) :
    (∑ i, x i * (x i + (r : ℝ) - 1 - 2 * (i : ℕ))) =
      N ^ 2 / r + (∑ i, (x i - N / r) ^ 2) +
        ∑ i, ∑ j ∈ Finset.Ioi i, (x i - x j) := by
  rw [root_gap_sum_eq_linear]
  have hc := centered_square_sum_eq Finset.univ x N (r : ℝ)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)) (by simp) hsum
  rw [hc]
  have hexpand : (∑ i, x i * (x i + (r : ℝ) - 1 - 2 * (i : ℕ))) =
      (∑ i, (x i) ^ 2) + ∑ i, x i * ((r : ℝ) - 1 - 2 * (i : ℕ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand]
  ring

/-- The second-moment estimate from the Casimir calculation. The two
representation-theoretic identities are exposed as `hdecomp` and `htrace`;
normalization and positivity then give the manuscript's constant exactly. -/
theorem second_moment_le_of_casimir {ι : Type*} (S : Finset ι)
    (p variance gap casimir : ι → ℝ) (N r : ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) (hnorm : ∑ i ∈ S, p i = 1)
    (hgap : ∀ i ∈ S, 0 ≤ gap i)
    (hdecomp : ∀ i ∈ S, casimir i = N ^ 2 / r + variance i + gap i)
    (htrace : ∑ i ∈ S, p i * casimir i = N * r + N * (N - 1) / r) :
    (∑ i ∈ S, p i * variance i) ≤ N * (r - 1 / r) := by
  have hpoint : ∑ i ∈ S, p i * (N ^ 2 / r + variance i) ≤
      ∑ i ∈ S, p i * casimir i := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hp i hi)
    rw [hdecomp i hi]
    exact le_add_of_nonneg_right (hgap i hi)
  have hexpand : (∑ i ∈ S, p i * (N ^ 2 / r + variance i)) =
      N ^ 2 / r + ∑ i ∈ S, p i * variance i := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul]
  rw [hexpand, htrace] at hpoint
  have harith : N * r + N * (N - 1) / r - N ^ 2 / r = N * (r - 1 / r) := by
    ring
  linarith

/-- The flat Young-law second-moment bound. Apart from the distribution and
partition hypotheses, the only imported representation-theoretic input is
the Casimir expectation identity `htrace`. The polynomial decomposition
and its nonnegative remainder are proved above. -/
theorem flat_young_second_moment_bound {ι : Type*} (S : Finset ι)
    (r : ℕ) (N : ℝ) (p : ι → ℝ) (row : ι → Fin r → ℝ)
    (hr : 0 < r) (hp : ∀ μ ∈ S, 0 ≤ p μ) (hnorm : ∑ μ ∈ S, p μ = 1)
    (hrowsum : ∀ μ ∈ S, ∑ i, row μ i = N)
    (horder : ∀ μ ∈ S, ∀ i j, i ≤ j → row μ j ≤ row μ i)
    (htrace :
      (∑ μ ∈ S, p μ * (∑ i, row μ i * (row μ i + (r : ℝ) - 1 - 2 * (i : ℕ)))) =
        N * r + N * (N - 1) / r) :
    (∑ μ ∈ S, p μ * (∑ i, (row μ i - N / r) ^ 2)) ≤ N * (r - 1 / r) := by
  apply second_moment_le_of_casimir S p
    (fun μ => ∑ i, (row μ i - N / r) ^ 2)
    (fun μ => ∑ i, ∑ j ∈ Finset.Ioi i, (row μ i - row μ j))
    (fun μ => ∑ i, row μ i * (row μ i + (r : ℝ) - 1 - 2 * (i : ℕ)))
    N r hp hnorm
  · intro μ hμ
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j hj
    exact sub_nonneg.mpr (horder μ hμ i j (Finset.mem_Ioi.mp hj).le)
  · intro μ hμ
    exact casimir_polynomial_eq_centered r (row μ) N hr (hrowsum μ hμ)
  · exact htrace

end Cloning.Projector
