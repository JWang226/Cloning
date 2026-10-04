import Cloning.CountMultinomialLimit
import Cloning.PCTPhysicalState
import Cloning.PCTTangentChartFrame
import Cloning.PCTJointGaussianChart

/-! Actual computational probabilities of the PCT Gaussian product particles. -/
noncomputable section
open scoped BigOperators Topology Classical Matrix ComplexOrder InnerProductSpace
open Filter MeasureTheory
namespace Cloning.PCTCount
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState Cloning.PCTLocalChart
open Cloning.PCTGaussianCovariance Cloning.PCTJointGaussianLaw Cloning.PCTJointGaussianWhitening
open Cloning.YoungGeneral Cloning.YoungHyperplane
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d s : ℕ}

def particleProbability
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (z : Fin s → ℂ) (L : ℕ) (i : Fin (d+1)) : ℝ :=
  (reducedDensityMatrix (frameParticle u z L) i i).re

theorem particleProbability_nonneg
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (z : Fin s → ℂ) (L : ℕ) (i : Fin (d+1)) : 0≤particleProbability u z L i :=
  (Complex.nonneg_iff.mp ((reducedDensityMatrix_posSemidef (frameParticle u z L)).diag_nonneg (i := i))).1

theorem particleProbability_sum
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (z : Fin s → ℂ) (L : ℕ) : ∑ i, particleProbability u z L i=1 := by
  have hh := congrArg Complex.re (trace_reducedDensityMatrix_complex (frameParticle u z L))
  simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, frameParticle_norm u.orthonormal z L,
    one_pow, Complex.one_re] using hh

def tangentScore
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (p : Fin (d+1) → ℝ) (hu : u 0=coefficientVector (schmidtCoefficients p))
    (z : Fin s → ℂ) : rootSpace d :=
  ⟨WithLp.toLp 2 (tangentClassical u p z), tangentClassical_sum_zero u p hu z⟩

theorem particleProbability_exact
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0≤p i)
    (hu : u 0=coefficientVector (schmidtCoefficients p))
    (z : Fin s → ℂ) (L : ℕ) (i : Fin (d+1)) :
    particleProbability u z L i=
      (p i+sampleScale L*tangentClassical u p z i+
        sampleScale L^2*(((frameTangentMatrix u z)*(frameTangentMatrix u z)ᴴ) i i).re)/
        (1+sampleScale L^2*‖coefficientVector (frameTangentMatrix u z)‖^2) := by
  unfold particleProbability
  rw [← normalizedTangentVector_eq_frameParticle u p hu z L,
    normalizedTangent_reduced_exact p hp _ _ (sq_nonneg _) (sampleScale L)]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_apply_eq,
    partialTraceDifferential_diagonal, Complex.add_re, Complex.smul_re,
    Complex.ofReal_re, tangentClassical, classicalCoordinate, smul_eq_mul]
  ring

theorem particleProbability_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0≤p i)
    (hu : u 0=coefficientVector (schmidtCoefficients p))
    (z : Fin s → ℂ) (i : Fin (d+1)) :
    Tendsto (fun L ↦ particleProbability u z L i) atTop (𝓝 (p i)) := by
  simp_rw [particleProbability_exact u p hp hu z]
  have hh := (((tendsto_const_nhds (x := p i)).add (sampleScale_tendsto.mul_const (tangentClassical u p z i))).add
    ((sampleScale_tendsto.pow 2).mul_const (((frameTangentMatrix u z)*(frameTangentMatrix u z)ᴴ) i i).re)).div
      ((tendsto_const_nhds (x := (1:ℝ))).add ((sampleScale_tendsto.pow 2).mul_const
        (‖coefficientVector (frameTangentMatrix u z)‖^2))) (by norm_num)
  simpa using hh

private theorem scaled_rational_difference (t a p b e v : ℝ)
    (ht : a*t=1) (hd : 1+t^2*e≠0) :
    a*((p+t*v+t^2*b)/(1+t^2*e)-p)=(v+t*(b-p*e))/(1+t^2*e) := by
  calc
    _ = (a*t)*(v+t*(b-p*e))/(1+t^2*e) := by field_simp; ring
    _ = _ := by rw [ht, one_mul]

theorem particleProbability_scaled_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0≤p i)
    (hu : u 0=coefficientVector (schmidtCoefficients p))
    (z : Fin s → ℂ) (i : Fin (d+1)) :
    Tendsto (fun L : ℕ ↦ Real.sqrt (L : ℝ)*(particleProbability u z L i-p i)) atTop
      (𝓝 (tangentClassical u p z i)) := by
  have hh := ((tendsto_const_nhds (x := tangentClassical u p z i)).add (sampleScale_tendsto.mul_const
    ((((frameTangentMatrix u z)*(frameTangentMatrix u z)ᴴ) i i).re-
      p i*‖coefficientVector (frameTangentMatrix u z)‖^2))).div
    ((tendsto_const_nhds (x := (1:ℝ))).add ((sampleScale_tendsto.pow 2).mul_const
      (‖coefficientVector (frameTangentMatrix u z)‖^2))) (by norm_num)
  simp only [zero_mul, zero_pow (by omega : 2≠0), add_zero, div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [particleProbability_exact u p hp hu z]
  symm
  apply scaled_rational_difference
  · rw [sampleScale, mul_inv_cancel₀ (by positivity : Real.sqrt (L : ℝ)≠0)]
  · positivity

/-- Conditional on the actual purification Gaussian tangent, count smoothing
converges in L¹ to the Gaussian translated by its literal diagonal score. -/
theorem conditional_count_density_l1_tendsto
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    (z : Fin s → ℂ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k ↦ ∫ x, |CountMultinomial.density d (n k) (particleProbability u z (n k))
      (particleProbability_nonneg u z (n k)) (particleProbability_sum u z (n k)) x-
        CountMultinomial.shiftedGaussian d (tangentScore u (flatSpectrum (d+1)) hu z) x|)
      atTop (𝓝 0) := by
  apply CountMultinomial.density_l1_tendsto d n hn
    (fun k ↦ particleProbability u z (n k)) (fun k ↦ particleProbability_nonneg u z (n k))
    (fun k ↦ particleProbability_sum u z (n k))
  · intro i
    exact (particleProbability_tendsto u (flatSpectrum (d+1))
      (fun _ ↦ by unfold flatSpectrum; positivity) hu z i).comp hn
  · intro i
    exact (particleProbability_scaled_tendsto u (flatSpectrum (d+1))
      (fun _ ↦ by unfold flatSpectrum; positivity) hu z i).comp hn

end Cloning.PCTCount
