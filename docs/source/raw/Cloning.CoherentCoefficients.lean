import Cloning.PoissonApproximation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Actual Hilbert-space number-amplitude vectors

Square roots of normalized nonnegative number laws define unit vectors in the
complex Hilbert space `ℓ²`. The concrete binomial and Poisson laws therefore
give unit number-amplitude vectors, and the former converge in Hilbert norm
to the latter. This uses the physical choice of excitation direction that
makes number amplitudes nonnegative; an occupation/Fock-space identification
and the associated quantum channel remain separate constructions.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace Cloning.CoherentCoefficients

variable {ι : Type*}

/-- The unit Hilbert vector with square-root probability amplitudes. -/
def amplitudeVector (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    lp (fun _ : ι => ℂ) 2 := by
  refine ⟨fun i => (Real.sqrt (p i) : ℂ), memℓp_gen ?_⟩
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp _)] using hs.summable

@[simp] theorem amplitudeVector_apply (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : HasSum p 1) (i : ι) : amplitudeVector p hp hs i = (Real.sqrt (p i) : ℂ) := rfl

theorem amplitudeVector_norm_sq (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : HasSum p 1) : ‖amplitudeVector p hp hs‖ ^ 2 = 1 := by
  calc
    _ = ∑' i, ‖amplitudeVector p hp hs i‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (amplitudeVector p hp hs))
    _ = ∑' i, p i := by
      apply tsum_congr
      intro i
      rw [amplitudeVector_apply, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hp i)]
    _ = 1 := hs.tsum_eq

theorem amplitudeVector_norm (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : HasSum p 1) : ‖amplitudeVector p hp hs‖ = 1 := by
  have h := amplitudeVector_norm_sq p hp hs
  nlinarith [norm_nonneg (amplitudeVector p hp hs)]

/-- Hilbert distance is exactly the square-root coefficient error. -/
theorem amplitudeVector_sub_norm (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hs : HasSum p 1) (ht : HasSum q 1) :
    ‖amplitudeVector p hp hs - amplitudeVector q hq ht‖ =
      Real.sqrt (∑' i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) := by
  have hsq : ‖amplitudeVector p hp hs - amplitudeVector q hq ht‖ ^ 2 =
      ∑' i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
    calc
      _ = ∑' i, ‖(amplitudeVector p hp hs - amplitudeVector q hq ht) i‖ ^ (2 : ℕ) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
            (amplitudeVector p hp hs - amplitudeVector q hq ht))
      _ = _ := by
        apply tsum_congr
        intro i
        simp only [lp.coeFn_sub, Pi.sub_apply, amplitudeVector_apply,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- A normalized pointwise probability limit gives an actual complex Hilbert
vector limit, without a finite-support assumption. -/
theorem amplitudeVector_tendsto (p : ℕ → ι → ℝ) (q : ι → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ i, 0 ≤ q i)
    (hs : ∀ n, HasSum (p n) 1) (ht : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => amplitudeVector (p n) (hp n) (hs n)) atTop
      (𝓝 (amplitudeVector q hq ht)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_eq_norm, amplitudeVector_sub_norm]
  simpa using (Real.continuous_sqrt.tendsto 0).comp
    (CountableScheffe.sqrt_amplitudes_tendsto_of_pointwise p q hp hq hs ht hpoint)

open PoissonApproximation

/-- The padded binomial number-amplitude vector. -/
def productVector (t : ℝ) (ht : 0 ≤ t) (L : ℕ) : lp (fun _ : ℕ => ℂ) 2 :=
  amplitudeVector (binomialWeight t L) (binomialWeight_nonneg ht L)
    (binomialWeight_hasSum ht L)

/-- The coherent Poisson number-amplitude vector. -/
def coherentVector (t : ℝ) (ht : 0 ≤ t) : lp (fun _ : ℕ => ℂ) 2 :=
  amplitudeVector (poissonWeight t) (poissonWeight_nonneg ht) (poissonWeight_hasSum ht)

/-- The Poisson amplitude has the usual coherent-vector exponential and
factorial coefficients. -/
theorem coherentVector_apply (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    coherentVector t ht j =
      ((Real.exp (-t / 2) * Real.sqrt t ^ j / Real.sqrt (j.factorial : ℝ) : ℝ) : ℂ) := by
  change (Real.sqrt (poissonWeight t j) : ℂ) = _
  congr 1
  unfold poissonWeight
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (Real.exp_nonneg _),
    ← Real.exp_half, Thermal.sqrt_nat_pow ht]

theorem productVector_norm (t : ℝ) (ht : 0 ≤ t) (L : ℕ) :
    ‖productVector t ht L‖ = 1 := amplitudeVector_norm _ _ _

theorem coherentVector_norm (t : ℝ) (ht : 0 ≤ t) :
    ‖coherentVector t ht‖ = 1 := amplitudeVector_norm _ _ _

/-- Concrete coherent-product convergence in the infinite-dimensional number
coefficient Hilbert space, including zero amplitude. -/
theorem productVector_tendsto_coherentVector (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (productVector t ht) atTop (𝓝 (coherentVector t ht)) :=
  amplitudeVector_tendsto _ _ (binomialWeight_nonneg ht) (poissonWeight_nonneg ht)
    (binomialWeight_hasSum ht) (poissonWeight_hasSum ht) (binomialWeight_tendsto t)

end Cloning.CoherentCoefficients
