import Cloning.PCTCountMeasurementSmoothing
import Cloning.PCTCountParameters
import Cloning.ChannelAveraging

/-! The measured density of the actual tensor-product Gaussian mixture is
exactly the conditional count mixture, with positivity and mass proved. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical
open MeasureTheory
namespace Cloning.PCTCountMeasurement
open Cloning.PCT Cloning.GeneralSymmetricOccupation Cloning.PCTReducedGaussian
open Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner Cloning.Hybrid
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.CountMultinomial
open Cloning.PCTPhysicalState Cloning.PCTCount Cloning.PCTLocalChart
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem measuredDensity_matrixTensorPower (d N : ℕ) (hN : 0<N)
    (ρ : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) (hdiag : ∀ i,ρ i i=(p i : ℂ))
    (x : rootSpace d) : measuredDensity d N (matrixTensorPower ρ N) x=density d N p hp hs x := by
  rw [measuredDensity_eq_clm d N hN, density_eq_word_sum d N hN]
  simp only [densityCLM, ContinuousLinearMap.smul_apply, smul_eq_mul, weightCLM_apply_any]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  have he (w : Word N (d+1)) :
      ⟪registerBasis (Word N (d+1)) w,(matrixTensorPower ρ N).1 (registerBasis _ w)⟫_ℂ =
        (wordWeight p w : ℂ) := by
    change matrixOf (registerBasis (Word N (d+1)))
      (ofMatrix (registerBasis (Word N (d+1))) (fun a c => ∏ i,ρ (a i) (c i))) w w = _
    rw [matrixOf_ofMatrix (registerBasis (Word N (d+1))).orthonormal]
    simp only [hdiag, ← Complex.ofReal_prod, wordWeight]
  unfold latticeWordLabel
  by_cases hw : sampleLabel d N (flatSpectrum (d+1)) x=shapeLattice d N (countShape w)
  · simp only [hw, if_true, he, Complex.ofReal_re]
  · simp only [hw, if_false, Ne.symm hw]

theorem measuredDensity_tensorState {d : ℕ} (ρ : Cloning.MatrixFidelity.State (Fin (d+1)))
    (N : ℕ) (hN : 0<N) (x : rootSpace d) :
    measuredDensity d N (tensorState ρ N).1 x = density d N (stateProbability ρ)
      (stateProbability_nonneg ρ) (stateProbability_sum ρ) x := by
  apply measuredDensity_matrixTensorPower d N hN
  intro i
  have hi := Complex.nonneg_iff.mp (ρ.positive.diag_nonneg (i := i))
  apply Complex.ext <;> simp [stateProbability,hi.2]

theorem measuredDensity_frameState {d s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (z : Fin s → ℂ) (N : ℕ) (hN : 0<N) (x : rootSpace d) :
    measuredDensity d N (frameState u z N).1 x=density d N (particleProbability u z N)
      (particleProbability_nonneg u z N) (particleProbability_sum u z N) x :=
  measuredDensity_tensorState (reducedState (frameParticle u z N) (frameParticle_norm u.orthonormal z N)) N hN x

theorem traceClass_integral_nonneg {H X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace X]
    (μ : Measure X) (A : X → TraceClass H) (hA : Integrable A μ) (hpos : ∀ x,0≤(A x).1) :
    0≤(∫ x,A x ∂μ).1 := by
  apply nonneg_of_inner_nonneg
  intro v
  have he := ((traceClassMatrixCoefficient v v).integral_comp_comm hA).symm
  change ⟪v,(∫ x,A x ∂μ).1 v⟫_ℂ = ∫ x,⟪v,(A x).1 v⟫_ℂ ∂μ at he
  rw [he]
  exact integral_complex_nonneg ((traceClassMatrixCoefficient v v).integrable_comp hA)
    (fun x => ((A x).1.nonneg_iff_isPositive.mp (hpos x)).inner_nonneg_right v)

theorem integral_frameState_nonneg {d s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (N : ℕ) (μ : Measure (Fin s → ℂ)) [IsFiniteMeasure μ] :
    0≤(∫ z,(frameState u z N).1 ∂μ).1 :=
  traceClass_integral_nonneg μ _ (integrable_frameState u N μ) (fun z => (frameState u z N).2)

theorem norm_integral_frameState {d s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (N : ℕ) (μ : Measure (Fin s → ℂ)) [IsProbabilityMeasure μ] :
    ‖∫ z,(frameState u z N).1 ∂μ‖=1 := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (integral_frameState_nonneg u N μ)]
  have he := ((Complex.reCLM.comp ((traceCLM : TraceClass (Register (Fin N → Fin (d+1))) →L[ℂ] ℂ).restrictScalars ℝ)).integral_comp_comm
    (integrable_frameState u N μ)).symm
  change (traceCLM (∫ z,(frameState u z N).1 ∂μ)).re=
    ∫ z,(traceCLM (frameState u z N).1).re ∂μ at he
  change (traceCLM (∫ z,(frameState u z N).1 ∂μ)).re=1
  rw [he]
  have ht z : (traceCLM (frameState u z N).1).re=1 := by
    exact (TraceClass.norm_eq_trace_re_of_nonneg _ (frameState u z N).2).symm.trans
      (norm_frameState u z N)
  simp only [ht, integral_const, probReal_univ, one_smul]

theorem measuredDensity_frameMixture {d s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1) × Fin (d+1))))
    (v : ℝ) (hv : 0<v) (N : ℕ) (hN : 0<N) (x : rootSpace d) :
    measuredDensity d N (∫ z,(frameState u z N).1 ∂gaussianProductMeasure (fun _ : Fin s => v)) x=
      ∫ z, density d N (particleProbability u z N) (particleProbability_nonneg u z N)
        (particleProbability_sum u z N) x ∂gaussianProductMeasure (fun _ : Fin s => v) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hv)
  rw [measuredDensity_integral _ d N hN _ (integrable_frameState u N _)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => measuredDensity_frameState u z N hN x))

end Cloning.PCTCountMeasurement
