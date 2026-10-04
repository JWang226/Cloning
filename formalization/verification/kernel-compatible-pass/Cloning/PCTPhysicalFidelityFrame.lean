import Cloning.PCTPhysicalFidelityLAN

/-! The exact physical frame particles satisfy both local mixed-LAN limits
once the explicitly stated genuine compact-window LAN property is supplied.
Their chart, compactness, trace constraint and limit coordinates are proved. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology Matrix.Norms.L2Operator
open MeasureTheory Filter NormedSpace Cloning.InfiniteTraceClass Cloning.Hybrid
namespace Cloning.PCTPhysicalFidelity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTLocalChart Cloning.PCTJointGaussianWhitening Cloning.PCTPhysicalState
open Cloning.PCTJointGaussianLaw Cloning.PCTGaussianOutput
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k d s : ℕ}

@[simp] theorem chartMatrix_zero (p : SimpleSpectrum (k+1)) (L : ℕ) :
    chartMatrix p 0 L = Matrix.diagonal (fun i => (p.eigenvalue i : ℂ)) := by
  have hY : orbitalGenerator p.eigenvalue 0 = 0 := by
    ext a b
    simp [orbitalGenerator]
  simp only [chartMatrix, Prod.fst_zero, Prod.snd_zero, hY, smul_zero, exp_zero,
    Pi.zero_apply, mul_zero, add_zero, neg_zero, Matrix.one_mul, Matrix.mul_one]

def baseState (p : SimpleSpectrum (k+1)) : Cloning.MatrixFidelity.State (Fin (k+1)) :=
  diagonalState p.eigenvalue (fun i => (p.positive i).le) p.normalized

@[simp] theorem chartTensor_zero (p : SimpleSpectrum (k+1)) (L : ℕ) :
    chartTensor p 0 L = (tensorState (baseState p) L).1 := by
  rw [chartTensor, chartMatrix_zero]
  rfl

theorem CompactWindowLAN.seed_limits
    {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e) :
    Tendsto (fun L => ‖(lan.forward L).map (tensorState (baseState p) L).1 - (reference p e).1‖)
      atTop (𝓝 0) ∧
    Tendsto (fun L => ‖(lan.reverse L).map (reference p e).1 - (tensorState (baseState p) L).1‖)
      atTop (𝓝 0) := by
  simpa only [chartTensor_zero, model_zero] using
    lan.moving_parameters (fun _ => 0) 0 tendsto_const_nhds {0} isCompact_singleton
      (by intro θ hθ; simp only [Set.mem_singleton_iff] at hθ; subst θ; simp)
      (Eventually.of_forall (fun _ => Set.mem_singleton 0))

def frameModel (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (u : Fin (s+1) → Register (Fin (k+1) × Fin (k+1))) (z : Fin s → ℂ) : HybridPositive k d :=
  model p b e (tangentParameters p.eigenvalue (frameTangentMatrix u z))

@[simp] theorem frameModel_val (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (u : Fin (s+1) → Register (Fin (k+1) × Fin (k+1))) (z : Fin s → ℂ) :
    (frameModel p b e u z).1 =
      hybridTranslation (whitenedJointTangent u p.eigenvalue b e z) (reference p e).1 := rfl

@[simp] theorem norm_frameModel (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (u : Fin (s+1) → Register (Fin (k+1) × Fin (k+1))) (z : Fin s → ℂ) :
    ‖(frameModel p b e u z).1‖ = 1 := norm_model _ _ _ _

theorem integrable_frameModel (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (u : Fin (s+1) → Register (Fin (k+1) × Fin (k+1)))
    (ν : Measure (Fin s → ℂ)) [IsFiniteMeasure ν] :
    Integrable (fun z => (frameModel p b e u z).1) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_hybridTranslation (reference p e).1).comp
      (continuous_whitenedJointTangent u p.eigenvalue b e)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z => (norm_frameModel p b e u z).le)

theorem CompactWindowLAN.frame_limits
    {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (k+1) × Fin (k+1))))
    (hu : u 0 = coefficientVector (schmidtCoefficients p.eigenvalue)) (z : Fin s → ℂ) :
    Tendsto (fun L => ‖(lan.forward L).map (frameState u z L).1 - (frameModel p b e u z).1‖)
      atTop (𝓝 0) ∧
    Tendsto (fun L => ‖(lan.reverse L).map (frameModel p b e u z).1 - (frameState u z L).1‖)
      atTop (𝓝 0) := by
  have horth : ⟪coefficientVector (schmidtCoefficients p.eigenvalue),
      coefficientVector (frameTangentMatrix u z)⟫_ℂ = 0 := by
    rw [coefficientVector_frameTangentMatrix, ← hu]
    exact frameTangent_orthogonal u.orthonormal z
  obtain ⟨K, hK, hzero, hmem⟩ := exists_compact_traceZero_sampleParameters p.eigenvalue
    p.strictAnti.injective (fun i => (p.positive i).le) p.normalized (frameTangentMatrix u z) horth
  have h := lan.moving_parameters
    (sampleParameters p.eigenvalue p.strictAnti.injective (frameTangentMatrix u z))
    (tangentParameters p.eigenvalue (frameTangentMatrix u z))
    (sampleParameters_tendsto _ _ _) K hK hzero hmem
  have he : ∀ᶠ L : ℕ in atTop,
      chartTensor p (sampleParameters p.eigenvalue p.strictAnti.injective (frameTangentMatrix u z) L) L =
        (frameState u z L).1 := by
    filter_upwards [eventually_frameParticle_exact_chart u p.eigenvalue p.strictAnti.injective
      (fun i => (p.positive i).le) hu (fun i j hij => sub_pos.mpr (p.strictAnti hij)) z] with L hL
    exact congrArg (fun M => matrixTensorPower M L) hL
  constructor
  · exact h.1.congr' (he.mono (fun L hL => by rw [hL]; rfl))
  · exact h.2.congr' (he.mono (fun L hL => by rw [hL]; rfl))

end Cloning.PCTPhysicalFidelity
