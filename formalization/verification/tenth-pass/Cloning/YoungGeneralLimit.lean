import Cloning.YoungGeneralTableaux

/-!
# Shrinking-window concentration for the general tableau formula

The window is the manuscript's `N^(-1/3)`.  Its atypical mass tends to zero
uniformly over the complete ordered probability simplex, including repeated
eigenvalues.  The only assumptions concern the spectrum itself.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungGeneral

def shrinkingRadius (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 / 3 : ℝ))

def concentrationEnvelope (d N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ (d * d) * (2 * d * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4))

theorem shrinkingRadius_nonneg (N : ℕ) : 0 ≤ shrinkingRadius N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem shrinkingRadius_le_one (N : ℕ) (hN : 1 ≤ N) : shrinkingRadius N ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)

theorem shrinkingRadius_tendsto_zero : Tendsto shrinkingRadius atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp tendsto_natCast_atTop_atTop

theorem sample_mul_radius_sq (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * shrinkingRadius N ^ 2 = (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold shrinkingRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  calc
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ) * 2) := by rw [Real.rpow_one]; norm_num
    _ = (N : ℝ) ^ (1 + -(1 / 3 : ℝ) * 2) := (Real.rpow_add hn _ _).symm
    _ = _ := by norm_num

/-- A fully explicit bound with no concentration or spectral-gap premise. -/
theorem atypicalMass_shrinking_le {d : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (horder : Antitone p) :
    atypicalMass N p (shrinkingRadius N) ≤ concentrationEnvelope d N := by
  have h := atypicalMass_le N p hp hs horder (shrinkingRadius N)
    (shrinkingRadius_nonneg N) ((shrinkingRadius_le_one N hN).trans (by norm_num))
  have heq : -(N : ℝ) * shrinkingRadius N ^ 2 / 4 = -((N : ℝ) ^ (1 / 3 : ℝ)) / 4 := by
    rw [neg_mul, sample_mul_radius_sq N (by omega)]
  simpa only [concentrationEnvelope, heq] using h

theorem concentrationEnvelope_nonneg (d N : ℕ) : 0 ≤ concentrationEnvelope d N := by
  unfold concentrationEnvelope
  positivity

/-- Polynomial factors are absorbed by the stretched exponential. -/
theorem concentrationEnvelope_tendsto_zero (d : ℕ) :
    Tendsto (concentrationEnvelope d) atTop (𝓝 0) := by
  let k := d * d
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hc := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 * (k : ℝ))
    (1 / 4 : ℝ) (by norm_num)).comp ht
  have hcore : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ k * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4))
      atTop (𝓝 0) := by
    convert hc using 1
    ext N
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    have he : (1 / 3 : ℝ) * (3 * (k : ℝ)) = k := by ring
    rw [he, Real.rpow_natCast]
    congr 1
    congr 1
    ring
  have hbound : Tendsto (fun N : ℕ ↦ (2 : ℝ) ^ k * (2 * d) *
      ((N : ℝ) ^ k * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4))) atTop (𝓝 0) := by
    simpa using hcore.const_mul ((2 : ℝ) ^ k * (2 * d))
  apply squeeze_zero' (Filter.Eventually.of_forall (concentrationEnvelope_nonneg d)) ?_ hbound
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : ((N : ℝ) + 1) ^ k ≤ (2 * (N : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ 2 * d * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4) by positivity)
  rw [mul_pow] at hh
  convert hh using 1 <;> dsimp [concentrationEnvelope, k] <;> ring

/-- Every fixed polynomial multiple of the tail envelope still vanishes.
This permits unbounded polynomial observables, such as reciprocal dimension
ratios, in later expectation estimates. -/
theorem polynomial_concentrationEnvelope_tendsto_zero (d q : ℕ) :
    Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) ^ q * concentrationEnvelope d N) atTop (𝓝 0) := by
  let k := q + d * d
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hc := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 * (k : ℝ))
    (1 / 4 : ℝ) (by norm_num)).comp ht
  have hcore : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ k * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4))
      atTop (𝓝 0) := by
    convert hc using 1
    ext N
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    have he : (1 / 3 : ℝ) * (3 * (k : ℝ)) = k := by ring
    rw [he, Real.rpow_natCast]
    congr 1
    congr 1
    ring
  have hbound : Tendsto (fun N : ℕ ↦ (2 : ℝ) ^ k * (2 * d) *
      ((N : ℝ) ^ k * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4))) atTop (𝓝 0) := by
    simpa using hcore.const_mul ((2 : ℝ) ^ k * (2 * d))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N ↦
    mul_nonneg (by positivity) (concentrationEnvelope_nonneg d N))) ?_ hbound
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : ((N : ℝ) + 1) ^ k ≤ (2 * (N : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ 2 * d * Real.exp (-((N : ℝ) ^ (1 / 3 : ℝ)) / 4) by positivity)
  rw [mul_pow] at hh
  convert hh using 1
  · simp only [concentrationEnvelope, k, pow_add]
    ring
  · ring

/-- Uniformity allows an arbitrary spectrum at each sample size. -/
theorem atypicalMass_tendsto_zero {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : ∀ N i, 0 ≤ p N i) (hs : ∀ N, ∑ i, p N i = 1)
    (horder : ∀ N, Antitone (p N)) :
    Tendsto (fun N ↦ atypicalMass N (p N) (shrinkingRadius N)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N ↦ atypicalMass_nonneg N (p N) (hp N) _))
    ?_ (concentrationEnvelope_tendsto_zero d)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact atypicalMass_shrinking_le N hN (p N) (hp N) (hs N) (horder N)

end Cloning.YoungGeneral
