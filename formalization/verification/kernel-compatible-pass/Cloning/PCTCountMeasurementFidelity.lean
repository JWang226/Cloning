import Cloning.PCTCountMeasurementChannel
import Cloning.MatrixFidelityScaling

/-! Actual quantum root fidelity is bounded above by the classical affinity
of any finite coarse computational measurement. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Classical ComplexOrder
namespace Cloning.PCTCountMeasurement
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
open Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem measuredMatrix_eq_diagonal_real (label : I → J) (A : TraceClass (Register I)) (hA : 0≤A.1) :
    measuredMatrix label (matrixOf (registerBasis I) A.1) =
      Matrix.diagonal (fun j => (weightCLM (registerBasis I) label j A : ℂ)) := by
  unfold measuredMatrix
  congr 1
  funext j
  rw [weightCLM_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : label i=j
  · simp only [if_pos hi, matrixOf]
    have hp := Complex.nonneg_iff.mp
      ((A.1.nonneg_iff_isPositive.mp hA).inner_nonneg_right (registerBasis I i))
    apply Complex.ext <;> simp [hp.2]
  · simp only [if_neg hi, Complex.ofReal_zero]

theorem measurementChannel_positive_apply (label : I → J) (A : TraceClass (Register I)) (hA : 0≤A.1) :
    (measurementChannel label).toLinearMap A =
      registerLiftCLM (Matrix.diagonal (fun j => (weightCLM (registerBasis I) label j A : ℂ))) := by
  rw [measurementChannel_apply, measuredMatrix_eq_diagonal_real label A hA]

theorem measurementChannel_rootFidelity (label : I → J) (A B : PositiveTraceClass (Register I)) :
    (A.map (measurementChannel label).toPositiveTracePreservingMap).rootFidelity
      (B.map (measurementChannel label).toPositiveTracePreservingMap) =
      ∑ j, Real.sqrt (weightCLM (registerBasis I) label j A.1 * weightCLM (registerBasis I) label j B.1) := by
  let C := A.map (measurementChannel label).toPositiveTracePreservingMap
  let D := B.map (measurementChannel label).toPositiveTracePreservingMap
  have heA : C.1 = registerLiftCLM (Matrix.diagonal (fun j => (weightCLM (registerBasis I) label j A.1 : ℂ))) :=
    measurementChannel_positive_apply label A.1 A.2
  have heB : D.1 = registerLiftCLM (Matrix.diagonal (fun j => (weightCLM (registerBasis I) label j B.1 : ℂ))) :=
    measurementChannel_positive_apply label B.1 B.2
  have hmatA : matrixOf (registerBasis J) C.1.1 =
      Matrix.diagonal (fun j => (weightCLM (registerBasis I) label j A.1 : ℂ)) := by
    rw [heA]
    exact matrixOf_ofMatrix (registerBasis J).orthonormal _
  have hmatB : matrixOf (registerBasis J) D.1.1 =
      Matrix.diagonal (fun j => (weightCLM (registerBasis I) label j B.1 : ℂ)) := by
    rw [heB]
    exact matrixOf_ofMatrix (registerBasis J).orthonormal _
  have hf := Cloning.InfiniteFidelityHilbertSum.rootFidelity_matrixOf_basis
    (registerBasis J).toOrthonormalBasis C D
  simp only [HilbertBasis.coe_toOrthonormalBasis] at hf
  rw [hmatA, hmatB, Cloning.MatrixFidelity.fidelity_diagonal_real _ _
    (fun j => weightCLM_nonneg _ label j A.1 A.2) (fun j => weightCLM_nonneg _ label j B.1 B.2)] at hf
  change C.rootFidelity D = _
  rw [← hf]
  apply Finset.sum_congr rfl
  intro j _
  exact (Real.sqrt_mul (weightCLM_nonneg _ label j A.1 A.2) _).symm

/-- Finite count measurement is an actual CPTP map, hence this upper bound
uses full quantum data processing rather than a diagonal-state assumption. -/
theorem rootFidelity_le_measurement_affinity (label : I → J) (A B : PositiveTraceClass (Register I)) :
    A.rootFidelity B ≤ ∑ j, Real.sqrt
      (weightCLM (registerBasis I) label j A.1 * weightCLM (registerBasis I) label j B.1) := by
  have h := Cloning.InfiniteFidelity.fidelity_data_processing (measurementChannel label) A.1 B.1 A.2 B.2
  change A.rootFidelity B ≤ (A.map (measurementChannel label).toPositiveTracePreservingMap).rootFidelity
    (B.map (measurementChannel label).toPositiveTracePreservingMap) at h
  exact h.trans_eq (measurementChannel_rootFidelity label A B)

end Cloning.PCTCountMeasurement
