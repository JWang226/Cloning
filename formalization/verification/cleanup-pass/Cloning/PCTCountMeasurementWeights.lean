import Cloning.InfiniteChannelCovariance
import Cloning.InfiniteTraceClassChannels
import Cloning.InfiniteFidelityHilbertSum

/-! Actual finite coarse computational measurement weights, their exact mass,
trace-norm contraction, and commutation with Bochner mixtures. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical
open MeasureTheory
namespace Cloning.PCTCountMeasurement
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [Fintype J]

def weightCLM (b : I → H) (label : I → J) (j : J) : TraceClass H →L[ℝ] ℝ :=
  ∑ i, if label i=j then Complex.reCLM.comp ((traceClassMatrixCoefficient (b i) (b i)).restrictScalars ℝ) else 0

@[simp] theorem weightCLM_apply (b : I → H) (label : I → J) (j : J) (A : TraceClass H) :
    weightCLM b label j A = ∑ i, if label i=j then (⟪b i, A.1 (b i)⟫_ℂ).re else 0 := by
  simp only [weightCLM, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : label i=j
  · simp only [if_pos hi]
    rfl
  · simp only [if_neg hi, ContinuousLinearMap.zero_apply]

theorem weightCLM_nonneg (b : I → H) (label : I → J) (j : J) (A : TraceClass H) (hA : 0≤A.1) :
    0≤weightCLM b label j A := by
  rw [weightCLM_apply]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (Complex.nonneg_iff.mp ((A.1.nonneg_iff_isPositive.mp hA).inner_nonneg_right (b i))).1
  · exact le_rfl

theorem weightCLM_sum (b : OrthonormalBasis I ℂ H) (label : I → J) (A : TraceClass H) :
    (∑ j, weightCLM b label j A) = (traceCLM A).re := by
  letI := b.toBasis.finiteDimensional_of_finite
  simp only [weightCLM_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [traceCLM_apply, trace_eq_linearMap_trace_of_finiteDimensional,
    LinearMap.trace_eq_sum_inner A.1.toLinearMap b, Complex.re_sum]
  rfl

theorem sum_abs_weightCLM_le (b : OrthonormalBasis I ℂ H) (label : I → J)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    (∑ j, |weightCLM b label j A|) ≤ ‖A‖ := by
  let P := TraceClass.positivePart A hA
  let N := TraceClass.negativePart A hA
  have hP : 0≤P.1 := TraceClass.positivePart_nonneg A hA
  have hN : 0≤N.1 := TraceClass.negativePart_nonneg A hA
  have he j : weightCLM b label j A = weightCLM b label j P - weightCLM b label j N := by
    rw [← map_sub]
    exact congrArg (weightCLM b label j) (TraceClass.positivePart_sub_negativePart A hA).symm
  simp_rw [he]
  calc
    (∑ j, |weightCLM b label j P-weightCLM b label j N|) ≤
        ∑ j, (weightCLM b label j P+weightCLM b label j N) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_of_nonneg (weightCLM_nonneg b label j P hP),
        abs_of_nonneg (weightCLM_nonneg b label j N hN)] using
        abs_sub (weightCLM b label j P) (weightCLM b label j N)
    _ = ‖P‖+‖N‖ := by
      rw [Finset.sum_add_distrib, weightCLM_sum, weightCLM_sum,
        TraceClass.norm_eq_trace_re_of_nonneg P hP, TraceClass.norm_eq_trace_re_of_nonneg N hN]
      rfl
    _ = ‖A‖ := TraceClass.norm_positivePart_add_norm_negativePart A hA

/-- The actual measured finite laws contract trace distance. -/
theorem weightCLM_l1_contraction (b : OrthonormalBasis I ℂ H) (label : I → J)
    (A B : TraceClass H) (hA : 0≤A.1) (hB : 0≤B.1) :
    (∑ j, |weightCLM b label j A-weightCLM b label j B|) ≤ ‖A-B‖ := by
  simp_rw [← map_sub]
  exact sum_abs_weightCLM_le b label (A-B)
    ((IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB))

/-- Finite measurement is a bounded real-linear evaluation, so it commutes
with the actual Bochner Gaussian mixture. -/
theorem weightCLM_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (b : I → H) (label : I → J) (j : J) (A : X → TraceClass H) (hA : Integrable A μ) :
    weightCLM b label j (∫ x, A x ∂μ) = ∫ x, weightCLM b label j (A x) ∂μ :=
  ((weightCLM b label j).integral_comp_comm hA).symm

end Cloning.PCTCountMeasurement
