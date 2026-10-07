import Cloning.PCTPurityFidelity
import Cloning.PCTPurityFidelityMixture
import Cloning.PCTCountMeasurementMixture
import Cloning.PCTRankAdaptedFlat
import Cloning.InfiniteFidelityHilbertSum
import Cloning.MatrixTraceOrder

/-! The purity estimate applied to the literal Gaussian-frame tensor mixture.
All finite normalization, positivity, matrix reconstruction, and overlap
identities are derived here; no purity limit is assumed. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder
open MeasureTheory
namespace Cloning.PCTPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPurificationChannel
open Cloning.PCTPhysicalState Cloning.InfiniteTraceClass Cloning.InfiniteFiniteCorner
open Cloning.Hybrid Cloning.PCTRankAdapted
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 250000
variable {d s : ℕ}

abbrev Frame (d s : ℕ) := OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1)×Fin (d+1)))

def frameMixtureMatrix (u : Frame d s) (μ : Measure (Fin s→ℂ)) (L : ℕ) :
    Matrix (Fin L→Fin (d+1)) (Fin L→Fin (d+1)) ℂ :=
  tensorMixtureMatrix μ (fun z => reducedDensityMatrix (frameParticle u z L)) L

theorem frameTensor_coefficient (u : Frame d s) (z : Fin s→ℂ) (L : ℕ)
    (i j : Fin L→Fin (d+1)) :
    traceClassMatrixCoefficient (registerBasis _ i) (registerBasis _ j) (frameState u z L).1=
      tensorPower L (reducedDensityMatrix (frameParticle u z L)) i j := by
  change matrixOf (registerBasis _) (ofMatrix (registerBasis _)
    (tensorPower L (reducedDensityMatrix (frameParticle u z L)))) i j=_
  rw [matrixOf_ofMatrix (registerBasis _).orthonormal]

theorem frameTensor_coefficient_integrable (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsFiniteMeasure μ] (L : ℕ) (i j : Fin L→Fin (d+1)) :
    Integrable (fun z => tensorPower L (reducedDensityMatrix (frameParticle u z L)) i j) μ := by
  simpa only [frameTensor_coefficient] using
    (traceClassMatrixCoefficient (registerBasis _ i) (registerBasis _ j)).integrable_comp
      (integrable_frameState u L μ)

theorem frameMixtureMatrix_eq_matrixOf (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsFiniteMeasure μ] (L : ℕ) :
    frameMixtureMatrix u μ L=matrixOf (registerBasis _) (∫ z,(frameState u z L).1 ∂μ).1 := by
  ext i j
  have he := (traceClassMatrixCoefficient (registerBasis _ i) (registerBasis _ j)).integral_comp_comm
    (integrable_frameState u L μ)
  simp only [frameTensor_coefficient] at he
  exact he

theorem frameMixtureMatrix_posSemidef (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsFiniteMeasure μ] (L : ℕ) : (frameMixtureMatrix u μ L).PosSemidef := by
  rw [frameMixtureMatrix_eq_matrixOf]
  exact matrixOf_posSemidef _ (Cloning.PCTCountMeasurement.integral_frameState_nonneg u L μ)

theorem frameMixtureMatrix_trace (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsProbabilityMeasure μ] (L : ℕ) : Matrix.trace (frameMixtureMatrix u μ L)=1 := by
  change (∑ i,∫ z,tensorPower L (reducedDensityMatrix (frameParticle u z L)) i i ∂μ)=1
  rw [←integral_finset_sum _ (fun i _ => frameTensor_coefficient_integrable u μ L i i)]
  have ht z : (∑i,tensorPower L (reducedDensityMatrix (frameParticle u z L)) i i)=(1:ℂ) := by
    change Matrix.trace (tensorPower L (reducedDensityMatrix (frameParticle u z L)))=1
    rw [trace_tensorPower,trace_reducedDensityMatrix_complex,frameParticle_norm u.orthonormal]
    norm_num
  simp only [ht,integral_const,probReal_univ,one_smul]

def frameMixtureState (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsProbabilityMeasure μ] (L : ℕ) : Cloning.MatrixFidelity.State (Fin L→Fin (d+1)) where
  matrix := frameMixtureMatrix u μ L
  positive := frameMixtureMatrix_posSemidef u μ L
  trace_one := frameMixtureMatrix_trace u μ L

def frameMixture (u : Frame d s) (μ : Measure (Fin s→ℂ)) [IsFiniteMeasure μ] (L : ℕ) :
    PositiveTraceClass (Register (Fin L→Fin (d+1))) :=
  ⟨∫ z,(frameState u z L).1 ∂μ,Cloning.PCTCountMeasurement.integral_frameState_nonneg u L μ⟩

theorem frameMixtureMatrix_purity (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsFiniteMeasure μ] (L : ℕ) :
    (Matrix.trace (frameMixtureMatrix u μ L*frameMixtureMatrix u μ L)).re=
      ∫ z,∫ w,(Matrix.trace (reducedDensityMatrix (frameParticle u z L)*
        reducedDensityMatrix (frameParticle u w L))).re^L ∂μ ∂μ := by
  apply tensorMixtureMatrix_purity_re μ _ L (frameTensor_coefficient_integrable u μ L)
  intro z w
  exact Cloning.MatrixFidelity.trace_mul_im_zero (reducedDensityMatrix_posSemidef _)
    (reducedDensityMatrix_posSemidef _)

theorem frameMixtureMatrix_scaled_purity (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsFiniteMeasure μ] (L : ℕ) :
    ((d+1:ℕ):ℝ)^L*(Matrix.trace (frameMixtureMatrix u μ L*frameMixtureMatrix u μ L)).re=
      ∫ z,∫ w,(((d+1:ℕ):ℝ)*(Matrix.trace (reducedDensityMatrix (frameParticle u z L)*
        reducedDensityMatrix (frameParticle u w L))).re)^L ∂μ ∂μ := by
  rw [frameMixtureMatrix_purity]
  simp_rw [mul_pow,integral_const_mul]

theorem flat_tensor_matrixOf (L : ℕ) :
    matrixOf (registerBasis (Fin L→Fin (d+1))) (tensorState (flatInternalState d) L).1.1=
      maximallyMixed (ι := Fin L→Fin (d+1)) := by
  change matrixOf (registerBasis _) (ofMatrix (registerBasis _)
    (tensorPower L (flatInternalState d).matrix))=_
  rw [matrixOf_ofMatrix (registerBasis _).orthonormal,maximallyMixed_diagonal]
  change tensorPower L (Matrix.diagonal (fun i : Fin (d+1) =>
    (Cloning.YoungGeneral.flatSpectrum (d+1) i : ℂ)))=_
  rw [tensorPower_diagonal]
  ext i j
  simp [Cloning.YoungGeneral.flatSpectrum,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_natCast]

theorem frameMixture_fidelity_purity_bound (u : Frame d s) (μ : Measure (Fin s→ℂ))
    [IsProbabilityMeasure μ] (L : ℕ) :
    1-((frameMixture u μ L).rootFidelity (tensorState (flatInternalState d) L))^2 ≤
      (∫ z,∫ w,(((d+1:ℕ):ℝ)*(Matrix.trace (reducedDensityMatrix (frameParticle u z L)*
        reducedDensityMatrix (frameParticle u w L))).re)^L ∂μ ∂μ)-1 := by
  have h := fidelity_purity_bound (frameMixtureState u μ L)
  have hF : Cloning.MatrixFidelity.fidelity (frameMixtureMatrix u μ L) maximallyMixed=
      (frameMixture u μ L).rootFidelity (tensorState (flatInternalState d) L) := by
    have hf := Cloning.InfiniteFidelityHilbertSum.rootFidelity_matrixOf_basis
      (registerBasis (Fin L→Fin (d+1))).toOrthonormalBasis
      (frameMixture u μ L) (tensorState (flatInternalState d) L)
    simp only [HilbertBasis.coe_toOrthonormalBasis] at hf
    have hM : matrixOf (registerBasis (Fin L→Fin (d+1))) (frameMixture u μ L).1.1=
        frameMixtureMatrix u μ L := (frameMixtureMatrix_eq_matrixOf u μ L).symm
    rw [hM,flat_tensor_matrixOf] at hf
    exact hf
  change 1-(Cloning.MatrixFidelity.fidelity (frameMixtureMatrix u μ L) maximallyMixed)^2≤_ at h
  rw [hF] at h
  simpa only [frameMixtureState,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,
    frameMixtureMatrix_scaled_purity] using h

end Cloning.PCTPurity
