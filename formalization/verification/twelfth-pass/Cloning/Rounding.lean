import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The elementary part of randomized Young-label dilation

This file checks the deterministic rounding estimates and finite-kernel
estimates used in Appendix `app:young-rounding` of `cloning.tex`.  Its last
section checks the three-error argument for dilation followed by averaging.
The analytic hypotheses in that section are explicit: neither the Young
local limit theorem nor the cellwise Poincaré estimate is asserted here.
-/

open scoped BigOperators
open Filter

namespace Cloning.Rounding

noncomputable def nearest (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

/-- The half-open cells are exactly the fibers of the rounding map. -/
theorem nearest_eq_iff (x : ℝ) (z : ℤ) :
    nearest x = z ↔ (z : ℝ) - 1 / 2 ≤ x ∧ x < (z : ℝ) + 1 / 2 := by
  rw [nearest, Int.floor_eq_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem nearest_error (x : ℝ) : |(nearest x : ℝ) - x| ≤ 1 / 2 := by
  have h := (nearest_eq_iff x (nearest x)).mp rfl
  rw [abs_le]
  constructor <;> linarith

/-- The first `d-1` coordinate errors in randomized rounding. -/
theorem dither_error (γ x y : ℝ) (hγ : 0 ≤ γ)
    (hy : -(1 / 2 : ℝ) ≤ y ∧ y < 1 / 2) :
    |(nearest (γ * (x + y)) : ℝ) - γ * x| ≤ (γ + 1) / 2 := by
  have hround := nearest_error (γ * (x + y))
  have habs : |y| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨hy.1, hy.2.le⟩
  calc
    |(nearest (γ * (x + y)) : ℝ) - γ * x| =
        |((nearest (γ * (x + y)) : ℝ) - γ * (x + y)) + γ * y| := by congr 1; ring
    _ ≤ |(nearest (γ * (x + y)) : ℝ) - γ * (x + y)| + |γ * y| := abs_add_le _ _
    _ ≤ 1 / 2 + γ * (1 / 2) := by rw [abs_mul, abs_of_nonneg hγ]; gcongr
    _ = (γ + 1) / 2 := by ring

/-- Completing the last coordinate preserves the required integer mass. -/
def completeLast {ι : Type*} [Fintype ι] (m : ℤ) (head : ι → ℤ) : ℤ :=
  m - ∑ i, head i

theorem completed_mass {ι : Type*} [Fintype ι] (m : ℤ) (head : ι → ℤ) :
    (∑ i, head i) + completeLast m head = m := by
  simp [completeLast]

/-- The last error is the negative sum of the head errors. -/
theorem completeLast_error {ι : Type*} [Fintype ι]
    (m : ℤ) (head : ι → ℤ) (μ : ι → ℝ) (μlast γ : ℝ)
    (hm : (m : ℝ) = γ * ((∑ i, μ i) + μlast)) :
    (completeLast m head : ℝ) - γ * μlast =
      -(∑ i, ((head i : ℝ) - γ * μ i)) := by
  simp only [completeLast, Int.cast_sub, Int.cast_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hm]
  ring

theorem completeLast_error_bound {ι : Type*} [Fintype ι]
    (m : ℤ) (head : ι → ℤ) (μ : ι → ℝ) (μlast γ c : ℝ)
    (hm : (m : ℝ) = γ * ((∑ i, μ i) + μlast))
    (hhead : ∀ i, |(head i : ℝ) - γ * μ i| ≤ c) :
    |(completeLast m head : ℝ) - γ * μlast| ≤ Fintype.card ι * c := by
  rw [completeLast_error m head μ μlast γ hm, abs_neg]
  calc
    |∑ i, ((head i : ℝ) - γ * μ i)| ≤ ∑ i, |(head i : ℝ) - γ * μ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ ↦ hhead i
    _ = Fintype.card ι * c := by simp

/-- The manuscript's `(d-1)(γ+1)/2` bound for the completed coordinate. -/
theorem rounded_last_error {ι : Type*} [Fintype ι]
    (m : ℤ) (μ y : ι → ℝ) (μlast γ : ℝ) (hγ : 0 ≤ γ)
    (hm : (m : ℝ) = γ * ((∑ i, μ i) + μlast))
    (hy : ∀ i, -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2) :
    |(completeLast m (fun i ↦ nearest (γ * (μ i + y i))) : ℝ) - γ * μlast| ≤
      Fintype.card ι * ((γ + 1) / 2) := by
  apply completeLast_error_bound m _ μ μlast γ _ hm
  exact fun i ↦ dither_error γ (μ i) (y i) hγ (hy i)

/-- A bounded unnormalized rounding error gives the claimed spectral error. -/
theorem normalized_rounding_error (μ ν n m γ p c : ℝ)
    (hn : n ≠ 0) (hm : 0 < m) (hscale : m = γ * n)
    (herr : |ν - γ * μ| ≤ c) :
    |ν / m - p| ≤ |μ / n - p| + c / m := by
  have hid : ν / m - p = (μ / n - p) + (ν - γ * μ) / m := by
    field_simp [hn, hm.ne']
    rw [hscale]
    ring
  rw [hid]
  calc
    |(μ / n - p) + (ν - γ * μ) / m| ≤
        |μ / n - p| + |(ν - γ * μ) / m| := abs_add_le _ _
    _ ≤ |μ / n - p| + c / m := by
      rw [abs_div, abs_of_pos hm]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right herr hm.le)

section FiniteKernels

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Nonnegative row-stochastic kernels, in real coordinates. -/
structure StochasticKernel (ι κ : Type*) [Fintype κ] where
  value : ι → κ → ℝ
  nonneg : ∀ i j, 0 ≤ value i j
  row_sum : ∀ i, ∑ j, value i j = 1

/-- The intersection-volume formula defines a stochastic kernel once the
target-cell overlaps partition the source-cell volume.  The geometric
partition-of-volume identity is supplied explicitly as `hpartition`. -/
noncomputable def kernelOfCellMasses (overlap : ι → κ → ℝ) (sourceVolume : ι → ℝ)
    (hoverlap : ∀ i j, 0 ≤ overlap i j)
    (hvolume : ∀ i, 0 < sourceVolume i)
    (hpartition : ∀ i, ∑ j, overlap i j = sourceVolume i) :
    StochasticKernel ι κ where
  value i j := overlap i j / sourceVolume i
  nonneg i j := div_nonneg (hoverlap i j) (hvolume i).le
  row_sum i := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hpartition i]
    exact mul_inv_cancel₀ (hvolume i).ne'

def transport (K : StochasticKernel ι κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i, p i * K.value i j

def l1Distance (p q : ι → ℝ) : ℝ := ∑ i, |p i - q i|

theorem transport_nonneg (K : StochasticKernel ι κ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (j : κ) : 0 ≤ transport K p j :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (K.nonneg i j)

theorem transport_mass (K : StochasticKernel ι κ) (p : ι → ℝ) :
    ∑ j, transport K p j = ∑ i, p i := by
  simp only [transport]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, K.row_sum, mul_one]

/-- Averaging by a stochastic kernel contracts the discrete `L¹` distance. -/
theorem transport_l1_contraction (K : StochasticKernel ι κ) (p q : ι → ℝ) :
    l1Distance (transport K p) (transport K q) ≤ l1Distance p q := by
  simp only [l1Distance, transport, ← Finset.sum_sub_distrib, ← sub_mul]
  calc
    (∑ j, |∑ i, (p i - q i) * K.value i j|) ≤
        ∑ j, ∑ i, |(p i - q i) * K.value i j| :=
      Finset.sum_le_sum fun j _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |p i - q i| := by
      simp only [abs_mul, abs_of_nonneg (K.nonneg _ _)]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, K.row_sum, mul_one]

/-- A bound for replacing a transition kernel without changing the input law. -/
theorem transport_kernel_error (K L : StochasticKernel ι κ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    l1Distance (transport K p) (transport L p) ≤
      ∑ i, p i * (∑ j, |K.value i j - L.value i j|) := by
  simp only [l1Distance, transport, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    (∑ j, |∑ i, p i * (K.value i j - L.value i j)|) ≤
        ∑ j, ∑ i, |p i * (K.value i j - L.value i j)| :=
      Finset.sum_le_sum fun j _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i * (∑ j, |K.value i j - L.value i j|) := by
      simp only [abs_mul, abs_of_nonneg (hp _)]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

omit [Fintype ι] in
theorem kernel_row_distance_le_two (K L : StochasticKernel ι κ) (i : ι) :
    (∑ j, |K.value i j - L.value i j|) ≤ 2 := by
  calc
    (∑ j, |K.value i j - L.value i j|) ≤
        ∑ j, (K.value i j + L.value i j) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        |K.value i j - L.value i j| ≤ |K.value i j| + |L.value i j| := abs_sub _ _
        _ = K.value i j + L.value i j := by
          rw [abs_of_nonneg (K.nonneg i j), abs_of_nonneg (L.nonneg i j)]
    _ = 2 := by rw [Finset.sum_add_distrib, K.row_sum, L.row_sum]; norm_num

/-- Fallback changes the output law by at most twice the atypical input mass. -/
theorem fallback_l1_bound (K L : StochasticKernel ι κ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (good : ι → Prop) [DecidablePred good]
    (hsame : ∀ i, good i → ∀ j, K.value i j = L.value i j) :
    l1Distance (transport K p) (transport L p) ≤
      2 * (∑ i, if good i then 0 else p i) := by
  calc
    l1Distance (transport K p) (transport L p) ≤
        ∑ i, p i * (∑ j, |K.value i j - L.value i j|) :=
      transport_kernel_error K L p hp
    _ ≤ ∑ i, 2 * (if good i then 0 else p i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : good i
      · simp [hi, hsame i hi]
      · simp only [hi, ↓reduceIte]
        calc
          p i * (∑ j, |K.value i j - L.value i j|) ≤ p i * 2 :=
            mul_le_mul_of_nonneg_left (kernel_row_distance_le_two K L i) (hp i)
          _ = 2 * p i := mul_comm _ _
    _ = 2 * (∑ i, if good i then 0 else p i) := (Finset.mul_sum _ _ _).symm

/-- Vanishing atypical mass makes the fallback asymptotically invisible in `L¹`. -/
theorem fallback_l1_tendsto
    (K L : ℕ → StochasticKernel ι κ) (p : ℕ → ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (good : ℕ → ι → Prop)
    [∀ n, DecidablePred (good n)]
    (hsame : ∀ n i, good n i → ∀ j, (K n).value i j = (L n).value i j)
    (hbad : Tendsto (fun n ↦ ∑ i, if good n i then 0 else p n i) atTop (nhds 0)) :
    Tendsto (fun n ↦ l1Distance (transport (K n) (p n)) (transport (L n) (p n)))
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun n ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg _)
    (fun n ↦ fallback_l1_bound (K n) (L n) (p n) (hp n) (good n) (hsame n))
  simpa [two_mul] using hbad.add hbad

end FiniteKernels

section AnalyticReduction

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The precise three-term inequality in the randomized dilation proof.
`D` is dilation, `A` is cell averaging, `f` is the input density, `g` the
input Gaussian, and `h` the limiting output Gaussian. -/
theorem dilation_averaging_error (D : E → F) (A : F → F)
    (hD : ∀ x y, ‖D x - D y‖ = ‖x - y‖)
    (hA : ∀ x y, ‖A x - A y‖ ≤ ‖x - y‖) (f g : E) (h : F) :
    ‖A (D f) - h‖ ≤ ‖f - g‖ + ‖A (D g) - D g‖ + ‖D g - h‖ := by
  calc
    ‖A (D f) - h‖ ≤ ‖A (D f) - A (D g)‖ + ‖A (D g) - h‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖D f - D g‖ + (‖A (D g) - D g‖ + ‖D g - h‖) :=
      add_le_add (hA _ _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = ‖f - g‖ + ‖A (D g) - D g‖ + ‖D g - h‖ := by rw [hD]; ring

/-- The three analytic inputs suffice to establish the rounded density limit.
This is a conditional reduction; in particular it does not claim to prove
the manuscript's Young local limit or Gaussian cell approximation. -/
theorem dilation_averaging_tendsto
    (D : ℕ → E → F) (A : ℕ → F → F) (f : ℕ → E) (g : E) (h : F)
    (hD : ∀ n x y, ‖D n x - D n y‖ = ‖x - y‖)
    (hA : ∀ n x y, ‖A n x - A n y‖ ≤ ‖x - y‖)
    (hlocal : Tendsto (fun n ↦ ‖f n - g‖) atTop (nhds 0))
    (hcell : Tendsto (fun n ↦ ‖A n (D n g) - D n g‖) atTop (nhds 0))
    (hscale : Tendsto (fun n ↦ ‖D n g - h‖) atTop (nhds 0)) :
    Tendsto (fun n ↦ ‖A n (D n (f n)) - h‖) atTop (nhds 0) := by
  apply squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ dilation_averaging_error (D n) (A n) (hD n) (hA n) (f n) g h)
  simpa using (hlocal.add hcell).add hscale

/-- Uniform version of the same reduction.  The parameter set `S` can be
the compact set of spectra in the manuscript.  Compactness enters through
the three uniform error bounds, rather than being silently assumed here. -/
theorem dilation_averaging_uniform {P : Type*} (S : Set P)
    (D : ℕ → P → E → F) (A : ℕ → P → F → F)
    (f : ℕ → P → E) (g : P → E) (h : P → F)
    (u v w : ℕ → ℝ)
    (hD : ∀ n p x y, ‖D n p x - D n p y‖ = ‖x - y‖)
    (hA : ∀ n p x y, ‖A n p x - A n p y‖ ≤ ‖x - y‖)
    (hlocal : ∀ n p, p ∈ S → ‖f n p - g p‖ ≤ u n)
    (hcell : ∀ n p, p ∈ S → ‖A n p (D n p (g p)) - D n p (g p)‖ ≤ v n)
    (hscale : ∀ n p, p ∈ S → ‖D n p (g p) - h p‖ ≤ w n)
    (hu : Tendsto u atTop (nhds 0)) (hv : Tendsto v atTop (nhds 0))
    (hw : Tendsto w atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ p ∈ S, ‖A n p (D n p (f n p)) - h p‖ < ε := by
  have hsum : Tendsto (fun n ↦ u n + v n + w n) atTop (nhds 0) := by
    simpa using (hu.add hv).add hw
  intro ε hε
  refine (hsum.eventually (gt_mem_nhds hε)).mono ?_
  intro n hn p hp
  calc
    ‖A n p (D n p (f n p)) - h p‖ ≤
        ‖f n p - g p‖ + ‖A n p (D n p (g p)) - D n p (g p)‖ +
          ‖D n p (g p) - h p‖ :=
      dilation_averaging_error (D n p) (A n p) (hD n p) (hA n p) _ _ _
    _ ≤ u n + v n + w n :=
      add_le_add (add_le_add (hlocal n p hp) (hcell n p hp)) (hscale n p hp)
    _ < ε := hn

end AnalyticReduction

end Cloning.Rounding
