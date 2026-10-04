import Cloning.PCTCountMeasurementImage
import Cloning.PCTCountMeasurementTensor
import Cloning.CountMultinomialMeasurability

/-! Exact cell smoothing of the physical computational count measurement.
Quantum fidelity and trace distance transfer to the measured densities. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical
open MeasureTheory
namespace Cloning.PCTCountMeasurement
open Cloning.PCT TensorLie Cloning.GeneralSymmetricOccupation
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.CountMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def latticeWordLabel (d N : ℕ) (w : Word N (d+1)) : Lattice d (N : ℤ) :=
  shapeLattice d N (countShape w)

def latticeWeight (d N : ℕ) (A : TraceClass (TensorRegister N (Fin (d+1)))) :
    Lattice d (N : ℤ) → ℝ := fun μ => weightCLM (registerBasis (Word N (d+1))) (latticeWordLabel d N) μ A

def measuredDensity (d N : ℕ) (A : TraceClass (TensorRegister N (Fin (d+1)))) : rootSpace d → ℝ :=
  sampleInterpolate d N (flatSpectrum (d+1)) (latticeWeight d N A)

def densityCLM (d N : ℕ) (x : rootSpace d) : TraceClass (TensorRegister N (Fin (d+1))) →L[ℝ] ℝ :=
  (Real.sqrt (N : ℝ)^d/Real.sqrt ((d : ℝ)+1)) •
    weightCLM (registerBasis (Word N (d+1))) (latticeWordLabel d N)
      (sampleLabel d N (flatSpectrum (d+1)) x)

theorem measuredDensity_eq_clm (d N : ℕ) (hN : 0<N)
    (A : TraceClass (TensorRegister N (Fin (d+1)))) (x : rootSpace d) :
    measuredDensity d N A x=densityCLM d N x A := by
  rw [measuredDensity, sampleInterpolate_eq_on_cell d N (by exact_mod_cast hN) _ _ _ x
    (mem_sampleCell_sampleLabel d N (flatSpectrum (d+1)) x)]
  simp only [latticeWeight, densityCLM, ContinuousLinearMap.smul_apply, smul_eq_mul]
  norm_cast

theorem latticeWeight_summable (d N : ℕ) (A : TraceClass (TensorRegister N (Fin (d+1)))) :
    Summable (latticeWeight d N A) := weightCLM_summable _ _ _

theorem latticeWeight_nonneg (d N : ℕ) (A : TraceClass (TensorRegister N (Fin (d+1))))
    (hA : 0≤A.1) (μ : Lattice d (N : ℤ)) : 0≤latticeWeight d N A μ :=
  weightCLM_nonneg_any _ _ _ hA μ

theorem measuredDensity_nonneg (d N : ℕ) (hN : 0<N)
    (A : TraceClass (TensorRegister N (Fin (d+1)))) (hA : 0≤A.1) (x : rootSpace d) :
    0≤measuredDensity d N A x := by
  rw [measuredDensity_eq_clm d N hN]
  change 0≤(Real.sqrt (N : ℝ)^d/Real.sqrt ((d : ℝ)+1))*_
  exact mul_nonneg (by positivity) (latticeWeight_nonneg d N A hA _)

theorem integral_measuredDensity (d N : ℕ) (hN : 0<N)
    (A : TraceClass (TensorRegister N (Fin (d+1)))) :
    (∫ x, measuredDensity d N A x)=(traceCLM A).re := by
  rw [measuredDensity, sampleInterpolate_integral d N (by exact_mod_cast hN) _ _
    (latticeWeight_summable d N A)]
  simpa only [latticeWeight, HilbertBasis.coe_toOrthonormalBasis] using
    weightCLM_tsum (registerBasis (Word N (d+1))).toOrthonormalBasis (latticeWordLabel d N) A

theorem measuredDensity_l1_contraction (d N : ℕ) (hN : 0<N)
    (A B : TraceClass (TensorRegister N (Fin (d+1)))) (hA : 0≤A.1) (hB : 0≤B.1) :
    (∫ x, |measuredDensity d N A x-measuredDensity d N B x|)≤‖A-B‖ := by
  rw [measuredDensity, measuredDensity, sampleInterpolate_l1_isometry d N
    (by exact_mod_cast hN) _ _ _ (latticeWeight_summable d N A) (latticeWeight_summable d N B)]
  simpa only [latticeWeight, HilbertBasis.coe_toOrthonormalBasis] using
    weightCLM_tsum_l1_contraction (registerBasis (Word N (d+1))).toOrthonormalBasis
      (latticeWordLabel d N) A B hA hB

theorem rootFidelity_le_measuredDensity_affinity (d N : ℕ) (hN : 0<N)
    (A B : PositiveTraceClass (TensorRegister N (Fin (d+1)))) :
    A.rootFidelity B ≤ ∫ x, Real.sqrt (measuredDensity d N A.1 x)*Real.sqrt (measuredDensity d N B.1 x) := by
  rw [measuredDensity, measuredDensity, sampleInterpolate_affinity d N
    (by exact_mod_cast hN) _ _ _ (latticeWeight_nonneg d N A.1 A.2)
    (latticeWeight_nonneg d N B.1 B.2) (latticeWeight_summable d N A.1) (latticeWeight_summable d N B.1)]
  exact rootFidelity_le_tsum_affinity (latticeWordLabel d N) A B

theorem measuredDensity_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (d N : ℕ) (hN : 0<N) (A : X → TraceClass (TensorRegister N (Fin (d+1))))
    (hA : Integrable A μ) (x : rootSpace d) :
    measuredDensity d N (∫ z, A z ∂μ) x=∫ z, measuredDensity d N (A z) x ∂μ := by
  simp_rw [measuredDensity_eq_clm d N hN]
  exact ((densityCLM d N x).integral_comp_comm hA).symm

/-- Integrability follows from the summable finite lattice law and the actual
coordinate change, for every complex trace-class input. -/
theorem integrable_measuredDensity (d N : ℕ) (hN : 0<N)
    (A : TraceClass (TensorRegister N (Fin (d+1)))) : Integrable (measuredDensity d N A) := by
  have hp : Summable (fun z => latticeWeight d N A (latticeCoordinates d N z)) :=
    (latticeCoordinates d N).summable_iff.mpr (latticeWeight_summable d N A)
  have hf := YoungRounding.integrable_affineDensity (Real.sqrt (N : ℝ))⁻¹
    (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hN)))
    ((coordinates d).symm (sampleAnchor d N (flatSpectrum (d+1))))
    (YoungRounding.integrable_interpolate hp)
  have hi : Integrable (interpolate d N (Real.sqrt (N : ℝ))⁻¹
      (sampleAnchor d N (flatSpectrum (d+1))) (latticeWeight d N A)) (coordinateMeasure d) := by
    apply ((coordinates_measurePreserving d).integrable_comp_emb
      (coordinatesContinuous d).toHomeomorph.measurableEmbedding).mp
    change Integrable (fun x => YoungRounding.affineDensity (Real.sqrt (N : ℝ))⁻¹
      ((coordinates d).symm (sampleAnchor d N (flatSpectrum (d+1))))
      (YoungRounding.interpolate (fun z => latticeWeight d N A (latticeCoordinates d N z)))
      ((coordinates d).symm (coordinates d x)))
    simpa only [LinearEquiv.symm_apply_apply] using hf
  unfold measuredDensity sampleInterpolate euclideanInterpolate
  rw [volume_eq_sqrt_smul_coordinateMeasure]
  exact (hi.const_mul _).smul_measure ENNReal.ofReal_ne_top

end Cloning.PCTCountMeasurement
