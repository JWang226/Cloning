import Cloning.MultimodeCoherent
import Cloning.CoherentGaussianMixture
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite multimode Gaussian coherent-state mixtures

The Bochner integral of the actual multimode coherent projector under independent
circular Gaussian coordinates equals the product-geometric occupation density.
The proof uses finite-product Fubini and the proved one-mode Gaussian moments;
the equality holds in the trace-class Banach space, including for zero modes.
-/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open MeasureTheory Cloning Cloning.InfiniteTraceClass

namespace Cloning.MultimodeCoherentGaussianMixture

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MultimodeCoherent

/-- Independent circular Gaussian amplitudes with the specified positive mean
squared amplitude in each mode. -/
def gaussianProductMeasure {d : ℕ} (s : Fin d → ℝ) : Measure (Fin d → ℂ) :=
  Measure.pi (fun i ↦ CoherentGaussianMixture.gaussianMeasure (s i))

theorem gaussianProductMeasure_probability {d : ℕ} {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) : IsProbabilityMeasure (gaussianProductMeasure s) := by
  letI (i : Fin d) : IsProbabilityMeasure (CoherentGaussianMixture.gaussianMeasure (s i)) :=
    CoherentGaussianMixture.gaussianMeasure_probability (hs i)
  unfold gaussianProductMeasure
  infer_instance

/-- The literal multimode occupation basis. -/
def numberBasis (d : ℕ) : HilbertBasis (Fin d → ℕ) ℂ (Fock d) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (Fock d))

@[simp] theorem numberBasis_eq_single {d : ℕ} (k : Fin d → ℕ) :
    numberBasis d k = lp.single 2 k 1 :=
  ((numberBasis d).repr_symm_single k).symm

theorem inner_numberBasis {d : ℕ} (k : Fin d → ℕ) (v : Fock d) :
    ⟪numberBasis d k, v⟫_ℂ = v k := by
  rw [numberBasis_eq_single, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

/-- Each matrix coefficient of the actual multimode rank-one operator is the
product of the corresponding one-mode coefficients. -/
theorem projector_coefficient {d : ℕ} (z : Fin d → ℂ) (n m : Fin d → ℕ) :
    ⟪numberBasis d n, (coherentProjector z).1 (numberBasis d m)⟫_ℂ =
      ∏ i, ComplexCoherent.coherentVector (z i) (n i) *
        star (ComplexCoherent.coherentVector (z i) (m i)) := by
  change ⟪numberBasis d n,
    (InnerProductSpace.rankOne ℂ (coherentVector z) (coherentVector z))
      (numberBasis d m)⟫_ℂ = _
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, inner_numberBasis,
    ← inner_conj_symm (coherentVector z) (numberBasis d m), inner_numberBasis]
  rw [mul_comm]
  simp only [coherentVector_apply, map_prod, Finset.prod_mul_distrib]
  rfl

/-- The operator integral exists in trace norm. -/
theorem integrable_coherentProjector_gaussian {d : ℕ} {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) : Integrable coherentProjector (gaussianProductMeasure s) := by
  letI := gaussianProductMeasure_probability hs
  exact integrable_coherentProjector _

/-- Fubini and the actual one-mode Gaussian moments evaluate every multimode
matrix coefficient. -/
theorem integral_coherent_coefficients {d : ℕ} {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) (n m : Fin d → ℕ) :
    (∫ z : Fin d → ℂ, ∏ i, ComplexCoherent.coherentVector (z i) (n i) *
      star (ComplexCoherent.coherentVector (z i) (m i)) ∂gaussianProductMeasure s) =
      if n = m then ((∏ i, Thermal.geometric (s i / (1 + s i)) (n i) : ℝ) : ℂ)
      else 0 := by
  classical
  letI (i : Fin d) : IsProbabilityMeasure (CoherentGaussianMixture.gaussianMeasure (s i)) :=
    CoherentGaussianMixture.gaussianMeasure_probability (hs i)
  rw [gaussianProductMeasure, integral_fin_nat_prod_eq_prod
    (μ := fun i : Fin d ↦ CoherentGaussianMixture.gaussianMeasure (s i))
    (fun i (z : ℂ) ↦ ComplexCoherent.coherentVector z (n i) *
      star (ComplexCoherent.coherentVector z (m i)))]
  simp_rw [CoherentGaussianMixture.integral_coherent_coefficients (hs _)]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true, Complex.ofReal_prod]
  · rw [if_neg hnm]
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ m i := by
      by_contra h
      apply hnm
      funext i
      exact not_not.mp (not_exists.mp h i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The actual Gaussian mixture in the trace-class Banach space. -/
def gaussianMixture {d : ℕ} (s : Fin d → ℝ) : TraceClass (Fock d) :=
  ∫ z : Fin d → ℂ, coherentProjector z ∂gaussianProductMeasure s

theorem gaussianMixture_coefficient {d : ℕ} {s : Fin d → ℝ}
    (hs : ∀ i, 0 < s i) (n m : Fin d → ℕ) :
    ⟪numberBasis d n, (gaussianMixture s).1 (numberBasis d m)⟫_ℂ =
      if n = m then ((∏ i, Thermal.geometric (s i / (1 + s i)) (n i) : ℝ) : ℂ)
      else 0 := by
  change traceClassMatrixCoefficient (numberBasis d n) (numberBasis d m)
    (gaussianMixture s) = _
  rw [gaussianMixture, ← ContinuousLinearMap.integral_comp_comm _
    (integrable_coherentProjector_gaussian hs)]
  simp_rw [traceClassMatrixCoefficient_apply, projector_coefficient]
  exact integral_coherent_coefficients hs n m

/-- Independent Gaussian mixing of actual multimode coherent projectors gives
the product-geometric density, with `qᵢ = sᵢ / (1 + sᵢ)`. This is an equality of
trace-class operators, not merely an equality of formal matrix coefficients. -/
theorem integral_coherentProjector_gaussian_eq_productThermal {d : ℕ}
    {s : Fin d → ℝ} (hs : ∀ i, 0 < s i) :
    (∫ z : Fin d → ℂ, coherentProjector z ∂gaussianProductMeasure s) =
      vectorMixture (numberBasis d)
        (fun k ↦ ∏ i, Thermal.geometric (s i / (1 + s i)) (k i)) := by
  classical
  have hq0 (i : Fin d) : 0 ≤ s i / (1 + s i) := by
    have hi := hs i
    positivity
  have hq1 (i : Fin d) : s i / (1 + s i) < 1 := by
    have hi := hs i
    exact (div_lt_one (by positivity)).mpr (by linarith)
  change gaussianMixture s = _
  apply Subtype.ext
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (numberBasis d).dense_span)
  rintro _ ⟨m, rfl⟩
  apply (numberBasis d).repr.injective
  ext n
  rw [(numberBasis d).repr_apply_apply, (numberBasis d).repr_apply_apply,
    InfiniteOccupationStates.vectorMixture_apply_basis (numberBasis d) _
      (Thermal.multimode_geometric_hasSum hq0 hq1).summable m, inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis d).orthonormal]
  rw [gaussianMixture_coefficient hs]
  by_cases hnm : n = m
  · subst n
    simp
  · simp [hnm]

end Cloning.MultimodeCoherentGaussianMixture
