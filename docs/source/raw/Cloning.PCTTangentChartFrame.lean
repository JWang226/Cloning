import Cloning.PCTTangentChartSamples

/-! Exact local-chart coordinates for the actual `frameParticle` vectors in
the physical PCT mixture. The sample scale is `1 / sqrt L`, with no additional
cloning gain applied to the limiting displacement. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace Topology BigOperators
open Matrix NormedSpace Filter
namespace Cloning.PCTLocalChart
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A : Type*} [Fintype A] [LinearOrder A] {s : ℕ}

/-- The normalized tangent curve is precisely the physical coherent-frame
particle, including its exact energy denominator. -/
theorem normalizedTangentVector_eq_frameParticle
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (p : A → ℝ)
    (hu : u 0 = coefficientVector (schmidtCoefficients p)) (z : Fin s → ℂ) (L : ℕ) :
    normalizedTangentVector p (frameTangentMatrix u z)
      (‖coefficientVector (frameTangentMatrix u z)‖ ^ 2) (sampleScale L) = frameParticle u z L := by
  rw [frameParticle_eq_normalized, normalizedTangentVector, frameTangentMatrix_energy u u.orthonormal,
    coefficientVector_add, coefficientVector_real_smul, coefficientVector_frameTangentMatrix, ← hu]
  have hs : sampleScale L ^ 2 = (L : ℝ)⁻¹ := by
    rw [sampleScale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg L)]
  rw [hs]
  have hd : 1 + (L : ℝ)⁻¹ * GeneralCoherent.energy z = 1 + GeneralCoherent.energy z / L := by ring
  rw [hd]
  simp only [one_div, sampleScale, ← Complex.coe_smul, Complex.ofReal_inv]

/-- The actual mixture frame determines a normalized Schmidt spectrum. -/
lemma frame_spectrum_sum_one
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A))) (p : A → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hu : u 0 = coefficientVector (schmidtCoefficients p)) :
    ∑ a, p a = 1 := by
  rw [← schmidt_norm_sq p hp0, ← hu, u.orthonormal.norm_eq_one]
  norm_num

/-- Exact local chart for the reduced physical PCT mixture particle. -/
theorem eventually_frameParticle_exact_chart
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : Function.Injective p) (hp0 : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j) (z : Fin s → ℂ) :
    ∀ᶠ L : ℕ in atTop,
      let H := sampleTangent p hp (frameTangentMatrix u z) L
      NormedSpace.exp (sampleScale L • orbitalGenerator p (orbitalCoordinates p H)) *
        Matrix.diagonal (fun i => ((p i + sampleScale L * spectralCoordinates H i : ℝ) : ℂ)) *
        NormedSpace.exp (-(sampleScale L • orbitalGenerator p (orbitalCoordinates p H))) =
        reducedDensityMatrix (frameParticle u z L) := by
  filter_upwards [eventually_sample_exact_chart p hp hp0 hgap (frameTangentMatrix u z)] with L hL
  simpa only [normalizedTangentVector_eq_frameParticle u p hu z L] using hL

/-- The exact frame-particle spectral parameters satisfy the LAN trace-zero
constraint and converge to its physical Gaussian score. -/
theorem frameParticle_spectral_parameters
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : Function.Injective p) (hp0 : ∀ a, 0 ≤ p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p)) (z : Fin s → ℂ) :
    (∀ᶠ L : ℕ in atTop,
      ∑ i, spectralCoordinates (sampleTangent p hp (frameTangentMatrix u z) L) i = 0) ∧
    Tendsto (fun L => spectralCoordinates (sampleTangent p hp (frameTangentMatrix u z) L))
      atTop (𝓝 (classicalCoordinate p (frameTangentMatrix u z))) := by
  refine ⟨?_, sampleSpectralCoordinates_tendsto p hp (frameTangentMatrix u z)⟩
  apply eventually_sample_spectral_sum_zero p hp hp0 (frame_spectrum_sum_one u p hp0 hu)
  rw [coefficientVector_frameTangentMatrix, ← hu]
  exact frameTangent_orthogonal u.orthonormal z

/-- The exact frame-particle orbital parameters converge to the displacement
used in the proved tangent Gaussian characteristic and thermal-output law. -/
theorem frameParticle_orbital_parameters
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : Function.Injective p) (z : Fin s → ℂ) :
    Tendsto (fun L => orbitalCoordinates p (sampleTangent p hp (frameTangentMatrix u z) L)) atTop
      (𝓝 (fun ij : OrbitalPair A => orbitalCoordinate p (frameTangentMatrix u z) ij.1.1 ij.1.2)) :=
  sampleOrbitalCoordinates_tendsto p hp (frameTangentMatrix u z)

end Cloning.PCTLocalChart
