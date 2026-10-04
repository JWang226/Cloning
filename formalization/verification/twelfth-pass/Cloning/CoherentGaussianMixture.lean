import Cloning.CoherentContinuity
import Cloning.ComplexGaussianMoments
import Cloning.InfiniteDiagonalFidelity
import Cloning.InfiniteChannelCovariance

/-! The circular Gaussian mixture of actual coherent rank-one density
operators, integrated in the genuine trace-class Banach space. -/

namespace Cloning.CoherentGaussianMixture

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Cloning Cloning.InfiniteTraceClass
open ComplexCoherent ComplexGaussianMoments
open scoped ComplexOrder InnerProductSpace Topology

/-- Circular Gaussian density of mean squared amplitude `s`. -/
def gaussianDensity (s : ℝ) (z : ℂ) : ℝ := Real.exp (-‖z‖ ^ 2 / s) / (Real.pi * s)

lemma gaussianDensity_pos {s : ℝ} (hs : 0 < s) (z : ℂ) : 0 < gaussianDensity s z :=
  div_pos (Real.exp_pos _) (mul_pos Real.pi_pos hs)

lemma continuous_gaussianDensity (s : ℝ) : Continuous (gaussianDensity s) := by
  unfold gaussianDensity
  fun_prop

lemma gaussianDensity_integral {s : ℝ} (hs : 0 < s) :
    (∫ z : ℂ, gaussianDensity s z) = 1 := by
  have h := radial_integral (1 / s) (div_pos zero_lt_one hs) 0
  simp only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add,
    pow_one, mul_one] at h
  have he (z : ℂ) : -‖z‖ ^ 2 / s = -(1 / s) * ‖z‖ ^ 2 := by ring
  simp_rw [gaussianDensity, he]
  rw [integral_div, h]
  field_simp

lemma integrable_gaussianDensity {s : ℝ} (hs : 0 < s) : Integrable (gaussianDensity s) :=
  integrable_of_integral_eq_one (gaussianDensity_integral hs)

/-- The Bochner integrand is integrable in trace norm, since every coherent
projector has trace norm one and the scalar density integrates to one. -/
lemma integrable_weighted_projector {s : ℝ} (hs : 0 < s) :
    Integrable (fun z : ℂ => gaussianDensity s z • coherentProjector z) := by
  apply (integrable_gaussianDensity hs).mono'
    ((continuous_gaussianDensity s).smul continuous_coherentProjector).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [norm_smul, coherentProjector_norm, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (gaussianDensity_pos hs z).le])

def gaussianMixture (s : ℝ) : TraceClass Fock :=
  ∫ z : ℂ, gaussianDensity s z • coherentProjector z

/-- A fixed canonical occupation basis on the coherent-state Fock space. -/
def numberBasis : HilbertBasis ℕ ℂ Fock :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fock)

@[simp] lemma numberBasis_eq_single (n : ℕ) : numberBasis n = lp.single 2 n 1 :=
  (numberBasis.repr_symm_single n).symm

lemma inner_numberBasis (n : ℕ) (v : Fock) : ⟪numberBasis n, v⟫_ℂ = v n := by
  rw [numberBasis_eq_single, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

lemma projector_coefficient (z : ℂ) (n m : ℕ) :
    ⟪numberBasis n, (coherentProjector z).1 (numberBasis m)⟫_ℂ =
      coherentVector z n * star (coherentVector z m) := by
  change ⟪numberBasis n, (InnerProductSpace.rankOne ℂ (coherentVector z) (coherentVector z))
    (numberBasis m)⟫_ℂ = _
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, inner_numberBasis,
    ← inner_conj_symm (coherentVector z) (numberBasis m), inner_numberBasis]
  exact mul_comm _ _

lemma weighted_coefficient (s : ℝ) (z : ℂ) (n m : ℕ) :
    (gaussianDensity s z : ℂ) * coherentVector z n * star (coherentVector z m) =
      (1 / (Real.pi * s * Real.sqrt (n.factorial : ℝ) * Real.sqrt (m.factorial : ℝ)) : ℂ) *
        ((Real.exp (-(1 + 1 / s) * ‖z‖ ^ 2) : ℂ) * z ^ n * star z ^ m) := by
  have he : Real.exp (-(1 + 1 / s) * ‖z‖ ^ 2) =
      Real.exp (-‖z‖ ^ 2 / s) * Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (-‖z‖ ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  rw [coherentVector_apply, coherentVector_apply]
  simp only [gaussianDensity, Complex.star_def, Complex.ofReal_mul, Complex.ofReal_div]
  rw [map_div₀, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

lemma gaussianMixture_coefficient {s : ℝ} (hs : 0 < s) (n m : ℕ) :
    ⟪numberBasis n, (gaussianMixture s).1 (numberBasis m)⟫_ℂ =
      (1 / (Real.pi * s * Real.sqrt (n.factorial : ℝ) * Real.sqrt (m.factorial : ℝ)) : ℂ) *
        ∫ z : ℂ, (Real.exp (-(1 + 1 / s) * ‖z‖ ^ 2) : ℂ) * z ^ n * star z ^ m := by
  rw [show ⟪numberBasis n, (gaussianMixture s).1 (numberBasis m)⟫_ℂ =
      traceClassMatrixCoefficient (numberBasis n) (numberBasis m) (gaussianMixture s) by rfl]
  rw [gaussianMixture, ← ContinuousLinearMap.integral_comp_comm _ (integrable_weighted_projector hs)]
  have he (z : ℂ) : traceClassMatrixCoefficient (numberBasis n) (numberBasis m)
      (gaussianDensity s z • coherentProjector z) =
      (gaussianDensity s z : ℂ) * coherentVector z n * star (coherentVector z m) := by
    rw [show gaussianDensity s z • coherentProjector z =
      (gaussianDensity s z : ℂ) • coherentProjector z by simp only [Complex.coe_smul], map_smul]
    rw [traceClassMatrixCoefficient_apply, projector_coefficient, smul_eq_mul, mul_assoc]
  simp_rw [he, weighted_coefficient]
  exact integral_const_mul _ _

lemma thermal_coefficient_algebra {s : ℝ} (hs : 0 < s) (n : ℕ) :
    1 / (Real.pi * s * Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) *
      (Real.pi * (n.factorial : ℝ) / (1 + 1 / s) ^ (n + 1)) =
      Thermal.geometric (s / (1 + s)) n := by
  have hs0 : s ≠ 0 := hs.ne'
  have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hf0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hd0 : (1 + s : ℝ) ≠ 0 := by positivity
  have he : 1 + 1 / s = (1 + s) / s := by field_simp; ring
  have hc : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
  have hden : Real.pi * s * Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ) =
      Real.pi * s * (n.factorial : ℝ) := by
    rw [mul_assoc (Real.pi * s), Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [hden, he, Thermal.geometric, hc, div_pow, div_pow, pow_succ, pow_succ]
  field_simp

lemma gaussianMixture_diagonal {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ⟪numberBasis n, (gaussianMixture s).1 (numberBasis n)⟫_ℂ =
      (Thermal.geometric (s / (1 + s)) n : ℂ) := by
  rw [gaussianMixture_coefficient hs, diagonal_integral _ (by positivity)]
  exact_mod_cast thermal_coefficient_algebra hs n

lemma gaussianMixture_offDiagonal {s : ℝ} (hs : 0 < s) (n m : ℕ) (hnm : n ≠ m) :
    ⟪numberBasis n, (gaussianMixture s).1 (numberBasis m)⟫_ℂ = 0 := by
  rw [gaussianMixture_coefficient hs, offDiagonal_integral _ n m hnm, mul_zero]

/-- The circular Gaussian coherent-state mixture equals the thermal operator
as an identity in the actual trace-class Banach space. -/
theorem gaussianMixture_eq_thermal {s : ℝ} (hs : 0 < s) :
    gaussianMixture s = vectorMixture numberBasis (Thermal.geometric (s / (1 + s))) := by
  have hq0 : 0 ≤ s / (1 + s) := by positivity
  have hq1 : s / (1 + s) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  apply Subtype.ext
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr numberBasis.dense_span)
  rintro _ ⟨m, rfl⟩
  apply numberBasis.repr.injective
  ext n
  rw [numberBasis.repr_apply_apply, numberBasis.repr_apply_apply,
    InfiniteOccupationStates.vectorMixture_apply_basis numberBasis _
      (Thermal.geometric_hasSum hq0 hq1).summable m, inner_smul_right,
    orthonormal_iff_ite.mp numberBasis.orthonormal]
  by_cases hnm : n = m
  · subst n
    rw [if_pos rfl, mul_one]
    exact gaussianMixture_diagonal hs m
  · rw [if_neg hnm, mul_zero]
    exact gaussianMixture_offDiagonal hs n m hnm

/-- The circular Gaussian measure, with its literal Lebesgue density. -/
def gaussianMeasure (s : ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (gaussianDensity s z))

lemma gaussianMeasure_probability {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (gaussianMeasure s) := by
  constructor
  rw [gaussianMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianDensity hs)
    (Filter.Eventually.of_forall (fun z => (gaussianDensity_pos hs z).le)), gaussianDensity_integral hs]
  exact ENNReal.ofReal_one

/-- The manuscript's positive coherent-state representation, as a Bochner
integral against the actual circular Gaussian probability measure. -/
theorem integral_coherentProjector_gaussian_eq_thermal {s : ℝ} (hs : 0 < s) :
    (∫ z : ℂ, coherentProjector z ∂gaussianMeasure s) =
      vectorMixture numberBasis (Thermal.geometric (s / (1 + s))) := by
  rw [gaussianMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_gaussianDensity s).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gaussianDensity_pos hs _).le]
  exact gaussianMixture_eq_thermal hs

lemma integrable_coherentProjector_gaussian {s : ℝ} (hs : 0 < s) :
    Integrable coherentProjector (gaussianMeasure s) := by
  letI := gaussianMeasure_probability hs
  exact integrable_coherentProjector _

/-- The exact scalar matrix coefficients of the circular Gaussian mixture,
exported for finite products of independent Gaussian coordinates. -/
lemma integral_coherent_coefficients {s : ℝ} (hs : 0 < s) (n m : ℕ) :
    (∫ z : ℂ, coherentVector z n * star (coherentVector z m) ∂gaussianMeasure s) =
      if n = m then (Thermal.geometric (s / (1 + s)) n : ℂ) else 0 := by
  have h := (traceClassMatrixCoefficient (numberBasis n) (numberBasis m)).integral_comp_comm
    (integrable_coherentProjector_gaussian hs)
  simp only [traceClassMatrixCoefficient_apply, projector_coefficient] at h
  rw [integral_coherentProjector_gaussian_eq_thermal hs] at h
  rw [h]
  have hq0 : 0 ≤ s / (1 + s) := by positivity
  have hq1 : s / (1 + s) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  rw [InfiniteOccupationStates.vectorMixture_apply_basis numberBasis _
    (Thermal.geometric_hasSum hq0 hq1).summable m, inner_smul_right,
    orthonormal_iff_ite.mp numberBasis.orthonormal]
  by_cases hnm : n = m
  · subst n
    simp
  · simp [hnm]

end
end Cloning.CoherentGaussianMixture
