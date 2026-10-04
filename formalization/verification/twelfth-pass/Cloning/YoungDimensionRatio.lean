import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete asymptotics of the crossing-root Weyl dimension product

For an `r`-row label in ambient dimension `r+k`, the manuscript's explicit
dimension-ratio expression is the product of `(rowᵢ+j-i)/(j-i)` over crossing
roots. This file defines that actual finite product and derives its uniform
relative-error bound directly from the row lengths. No dimension-ratio
convergence or product approximation is assumed.

The identification of this explicit Weyl product with dimensions of the
particular representation spaces is a separate representation-theoretic
statement. This file proves the analytic input once that formula is used.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungDimensionRatio

/-- The positive-root gap `j-i`, using zero-based indices on either side
of the rank boundary. Ambient dimension is `r+k`. -/
def crossingGap {r k : ℕ} (a : Fin r × Fin k) : ℝ :=
  (r : ℝ) + (a.2.val : ℝ) - (a.1.val : ℝ)

theorem crossingGap_pos {r k : ℕ} (a : Fin r × Fin k) : 0 < crossingGap a := by
  have hi : (a.1.val : ℝ) < r := by exact_mod_cast a.1.isLt
  have hj : 0 ≤ (a.2.val : ℝ) := Nat.cast_nonneg _
  dsimp [crossingGap]
  linarith

theorem crossingGap_le {r k : ℕ} (a : Fin r × Fin k) :
    crossingGap a ≤ (r : ℝ) + k := by
  have hj : (a.2.val : ℝ) < k := by exact_mod_cast a.2.isLt
  have hi : 0 ≤ (a.1.val : ℝ) := Nat.cast_nonneg _
  dsimp [crossingGap]
  linarith

/-- The manuscript's concrete crossing-root dimension-ratio product. -/
def dimensionRatio (r k : ℕ) (row : Fin r → ℝ) : ℝ :=
  ∏ a : Fin r × Fin k, (row a.1 + crossingGap a) / crossingGap a

/-- The exact leading coefficient `c_{r,r+k}`. -/
def leadingConstant (r k : ℕ) : ℝ :=
  ∏ a : Fin r × Fin k, 1 / ((r : ℝ) * crossingGap a)

theorem leadingConstant_pos (r k : ℕ) (hr : 0 < r) : 0 < leadingConstant r k := by
  apply Finset.prod_pos
  intro a _
  exact one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr hr) (crossingGap_pos a))

/-- An exact rescaling identity, before taking any limit. -/
theorem dimensionRatio_factorization (r k : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hN : 0 < N) :
    dimensionRatio r k row = leadingConstant r k * N ^ (r * k) *
      ∏ a : Fin r × Fin k, ((r : ℝ) * (row a.1 + crossingGap a) / N) := by
  have hfactor (a : Fin r × Fin k) :
      (row a.1 + crossingGap a) / crossingGap a =
        ((1 / ((r : ℝ) * crossingGap a)) * N) *
          ((r : ℝ) * (row a.1 + crossingGap a) / N) := by
    have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
    have hg : crossingGap a ≠ 0 := (crossingGap_pos a).ne'
    field_simp
  unfold dimensionRatio
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [leadingConstant, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]

/-- The per-root rescaled factor is uniformly close to one whenever the
row proportions are uniformly close to the flat spectrum. -/
theorem rescaled_factor_error (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 0 < N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ) (a : Fin r × Fin k) :
    |(r : ℝ) * (row a.1 + crossingGap a) / N - 1| ≤
      (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N := by
  have hr' : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have heq : (r : ℝ) * (row a.1 + crossingGap a) / N - 1 =
      (r : ℝ) * (row a.1 / N - 1 / (r : ℝ)) + (r : ℝ) * crossingGap a / N := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(r : ℝ) * (row a.1 / N - 1 / (r : ℝ))| +
        |(r : ℝ) * crossingGap a / N| := abs_add_le _ _
    _ = (r : ℝ) * |row a.1 / N - 1 / (r : ℝ)| + (r : ℝ) * crossingGap a / N := by
      rw [abs_mul, abs_of_pos hr', abs_of_nonneg
        (div_nonneg (mul_nonneg hr'.le (crossingGap_pos a).le) hN.le)]
    _ ≤ (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N := by
      apply add_le_add (mul_le_mul_of_nonneg_left (hclose a.1) hr'.le)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (crossingGap_le a) hr'.le) hN.le

/-- A uniform quantitative estimate for the actual Weyl ratio product.
The right-hand side tends to zero whenever `δ → 0` and `N → ∞`.
In particular, this proves uniform leading-order asymptotics on the
manuscript's typical row sets without assuming a product approximation. -/
theorem dimensionRatio_relative_error (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 0 < N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ) :
    |dimensionRatio r k row / (leadingConstant r k * N ^ (r * k)) - 1| ≤
      Real.exp ((r * k : ℕ) * ((r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N)) - 1 := by
  let f : Fin r × Fin k → ℝ := fun a => (r : ℝ) * (row a.1 + crossingGap a) / N
  have hden : leadingConstant r k * N ^ (r * k) ≠ 0 :=
    (mul_pos (leadingConstant_pos r k hr) (pow_pos hN _)).ne'
  rw [dimensionRatio_factorization r k row N hr hN, mul_div_cancel_left₀ _ hden]
  have hprod := Finset.norm_prod_one_add_sub_one_le Finset.univ (fun a => f a - 1)
  have hsum : (∑ a, |f a - 1|) ≤
      (r * k : ℕ) * ((r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N) := by
    calc
      _ ≤ ∑ _a : Fin r × Fin k,
          ((r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N) := by
        exact Finset.sum_le_sum (fun a _ => rescaled_factor_error r k row N δ hr hN hclose a)
      _ = _ := by simp [Fintype.card_prod]; ring
  have hp : |(∏ a, f a) - 1| ≤ Real.exp (∑ a, |f a - 1|) - 1 := by
    have h1 (a) : 1 + (f a - 1) = f a := by ring
    simpa only [h1, Real.norm_eq_abs] using hprod
  exact hp.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

/-- Nonnegative rows give a strictly positive dimension-ratio product. -/
theorem dimensionRatio_pos (r k : ℕ) (row : Fin r → ℝ)
    (hrow : ∀ i, 0 ≤ row i) : 0 < dimensionRatio r k row := by
  apply Finset.prod_pos
  intro a _
  exact div_pos (add_pos_of_nonneg_of_pos (hrow a.1) (crossingGap_pos a))
    (crossingGap_pos a)

/-- The explicit error envelope vanishes. This bound is independent of
the selected row vector, so it controls all typical labels simultaneously. -/
theorem error_envelope_tendsto_zero (r k : ℕ) (N δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n =>
      Real.exp ((r * k : ℕ) * ((r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n)) - 1)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hN
  have harg : Tendsto
      (fun n => (r * k : ℕ) * ((r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (((tendsto_const_nhds (x := (r : ℝ))).mul hδ).add
        ((tendsto_const_nhds (x := (r : ℝ) * ((r : ℝ) + k))).mul hinv)).const_mul
          ((r * k : ℕ) : ℝ)
  simpa only [Real.exp_zero, sub_self] using
    ((Real.continuous_exp.tendsto 0).comp harg).sub_const 1

/-- Leading-order normalization for the concrete Weyl ratio, derived
from row proximity and the proved quantitative estimate. -/
theorem normalized_dimensionRatio_tendsto_one (r k : ℕ) (hr : 0 < r)
    (row : ℕ → Fin r → ℝ) (N δ : ℕ → ℝ)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ n i, |row n i / N n - 1 / (r : ℝ)| ≤ δ n) :
    Tendsto (fun n => dimensionRatio r k (row n) /
      (leadingConstant r k * (N n) ^ (r * k))) atTop (𝓝 1) := by
  have hzero : Tendsto (fun n => dimensionRatio r k (row n) /
      (leadingConstant r k * (N n) ^ (r * k)) - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => by simpa only [Real.norm_eq_abs] using
        dimensionRatio_relative_error r k (row n) (N n) (δ n) hr (hNpos n) (hclose n))
    exact error_envelope_tendsto_zero r k N δ hN hδ
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1

/-- Exact scalar identity used to compare two independently rescaled
dimension products. -/
theorem ratio_rescaling (X Y c N M : ℝ) (a : ℕ)
    (hY : Y ≠ 0) (hc : c ≠ 0) (hN : N ≠ 0) (hM : M ≠ 0) :
    X / Y = ((X / (c * N ^ a)) / (Y / (c * M ^ a))) * (N / M) ^ a := by
  rw [div_pow]
  field_simp

/-- The concrete crossing-root products at sample sizes with ratio `γ`
have ratio limit `γ^(-r*k)`. Both normalization limits are derived above;
neither product limit is a hypothesis. -/
theorem dimensionRatio_quotient_tendsto (r k : ℕ) (hr : 0 < r)
    (rowIn rowOut : ℕ → Fin r → ℝ) (N M δ ε : ℕ → ℝ) (γ : ℝ)
    (hNpos : ∀ n, 0 < N n) (hMpos : ∀ n, 0 < M n)
    (hN : Tendsto N atTop atTop) (hγ : 0 < γ)
    (hratio : Tendsto (fun n => M n / N n) atTop (𝓝 γ))
    (hδ : Tendsto δ atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcloseIn : ∀ n i, |rowIn n i / N n - 1 / (r : ℝ)| ≤ δ n)
    (hcloseOut : ∀ n i, |rowOut n i / M n - 1 / (r : ℝ)| ≤ ε n)
    (hout : ∀ n i, 0 ≤ rowOut n i) :
    Tendsto (fun n => dimensionRatio r k (rowIn n) / dimensionRatio r k (rowOut n))
      atTop (𝓝 ((γ⁻¹) ^ (r * k))) := by
  have hM : Tendsto M atTop atTop := by
    have h := Filter.Tendsto.pos_mul_atTop hγ hratio hN
    apply h.congr'
    exact Filter.Eventually.of_forall (fun n => div_mul_cancel₀ _ (hNpos n).ne')
  have hin := normalized_dimensionRatio_tendsto_one r k hr rowIn N δ hNpos hN hδ hcloseIn
  have houtlim := normalized_dimensionRatio_tendsto_one r k hr rowOut M ε hMpos hM hε hcloseOut
  have hquot := hin.div houtlim one_ne_zero
  have hscale : Tendsto (fun n => N n / M n) atTop (𝓝 γ⁻¹) := by
    simpa only [inv_div] using hratio.inv₀ hγ.ne'
  have h := hquot.mul (hscale.pow (r * k))
  simp only [div_self one_ne_zero, one_mul] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  exact (ratio_rescaling _ _ _ _ _ _ (dimensionRatio_pos r k (rowOut n) (hout n)).ne'
    (leadingConstant_pos r k hr).ne' (hNpos n).ne' (hMpos n).ne').symm

/-- The explicit support-sector factor tends to the manuscript's
`γ^(-r(d-r)/2)`, with `d = r+k`. This is the analytic dimension-ratio input
to the projector-state cloning theorem. -/
theorem projector_sector_factor_tendsto (r k : ℕ) (hr : 0 < r)
    (rowIn rowOut : ℕ → Fin r → ℝ) (N M δ ε : ℕ → ℝ) (γ : ℝ)
    (hNpos : ∀ n, 0 < N n) (hMpos : ∀ n, 0 < M n)
    (hN : Tendsto N atTop atTop) (hγ : 0 < γ)
    (hratio : Tendsto (fun n => M n / N n) atTop (𝓝 γ))
    (hδ : Tendsto δ atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcloseIn : ∀ n i, |rowIn n i / N n - 1 / (r : ℝ)| ≤ δ n)
    (hcloseOut : ∀ n i, |rowOut n i / M n - 1 / (r : ℝ)| ≤ ε n)
    (hout : ∀ n i, 0 ≤ rowOut n i) :
    Tendsto (fun n => Real.sqrt (dimensionRatio r k (rowIn n) / dimensionRatio r k (rowOut n)))
      atTop (𝓝 (γ ^ (-((r * k : ℕ) : ℝ) / 2))) := by
  have h := (dimensionRatio_quotient_tendsto r k hr rowIn rowOut N M δ ε γ
    hNpos hMpos hN hγ hratio hδ hε hcloseIn hcloseOut hout).sqrt
  have hvalue : Real.sqrt ((γ⁻¹) ^ (r * k)) = γ ^ (-((r * k : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hγ.le),
      ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hvalue] at h
  exact h

end Cloning.YoungDimensionRatio
