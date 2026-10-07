import Cloning.GeneralCoherentChannels
import Cloning.MultimodeCoherentGaussianMixture
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual integration of the finite pure-product model against any finite
amplitude measure. The unbounded Gaussian parameter space needs no uniform
approximation hypothesis: unit trace supplies an integrable constant bound. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass
namespace Cloning.GeneralCoherent
open GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_oneParticle (s L : ℕ) (a : Fin (s + 1)) :
    Continuous (fun z : Fin s → ℂ => oneParticle z L a) := by
  have hd : Continuous (fun z : Fin s → ℂ =>
      (Real.sqrt (1 + energy z / L) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_const.add ((continuous_energy s).div_const _)))
  have hdn (z : Fin s → ℂ) : (Real.sqrt (1 + energy z / L) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by have := energy_nonneg z; positivity)).ne'
  refine Fin.cases ?_ (fun i => ?_) a
  · exact continuous_const.div hd hdn
  · exact ((continuous_apply i).div_const _).div hd hdn

theorem continuous_productTensor (s L : ℕ) : Continuous (fun z : Fin s → ℂ => productTensor z L) := by
  classical
  have he : (fun z : Fin s → ℂ => productTensor z L) =
      fun z => ∑ w : Word L (s + 1), (∏ i, oneParticle z L (w i)) •
        (lp.single 2 w 1 : TensorSpace L (s + 1)) := by
    funext z
    ext w
    simp [productTensor_apply, lp.single_apply, Pi.single_apply]
  rw [he]
  exact continuous_finset_sum _ (fun w _ =>
    (continuous_finset_prod _ (fun i _ => continuous_oneParticle s L (w i))).smul continuous_const)

theorem continuous_productProjector (s L : ℕ) :
    Continuous (fun z : Fin s → ℂ => vectorProjector (productTensor z L)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact vectorProjector_tendsto ((continuous_productTensor s L).tendsto z)

theorem integrable_productProjector {s : ℕ} (L : ℕ) (μ : Measure (Fin s → ℂ))
    [IsFiniteMeasure μ] : Integrable (fun z => vectorProjector (productTensor z L)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_productProjector s L).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    simp only [norm_vectorProjector, productTensor_norm, one_pow, le_refl])

/-- The literal mixture of physical tensor-power projectors. -/
def productMixture {s : ℕ} (L : ℕ) (μ : Measure (Fin s → ℂ)) :
    TraceClass (TensorSpace L (s + 1)) :=
  ∫ z, vectorProjector (productTensor z L) ∂μ

/-- The literal coherent-state mixture in the common Fock space. -/
def coherentMixture {s : ℕ} (μ : Measure (Fin s → ℂ)) : TraceClass (FockSpace s) :=
  ∫ z, MultimodeCoherent.coherentProjector z ∂μ

theorem occupationChannel_error_le_two {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖(occupationChannel L s).toLinearMap (MultimodeCoherent.coherentProjector z) -
      vectorProjector (productTensor z L)‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [(occupationChannel L s).toPositiveTracePreservingMap.norm_map_of_nonneg _
    (MultimodeCoherent.coherentProjector_nonneg z), MultimodeCoherent.coherentProjector_norm,
    norm_vectorProjector, productTensor_norm]
  norm_num

theorem occupationChannel_error_tendsto {s : ℕ} (z : Fin s → ℂ) :
    Tendsto (fun L => ‖(occupationChannel L s).toLinearMap
      (MultimodeCoherent.coherentProjector z) - vectorProjector (productTensor z L)‖)
      atTop (𝓝 0) := by
  have hp := productVector_moving_tendsto (fun L : ℕ => L) tendsto_id
    (fun _ => z) tendsto_const_nhds
  have ht : Tendsto (fun L => 2 * ‖productVector z L - MultimodeCoherent.coherentVector z‖)
      atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hp).const_mul 2
  exact squeeze_zero (fun _ => norm_nonneg _) (fun L => occupationChannel_coherent_distance_le z L) ht

theorem integrable_occupationChannel_error {s : ℕ} (L : ℕ) (μ : Measure (Fin s → ℂ))
    [IsFiniteMeasure μ] : Integrable (fun z =>
      ‖(occupationChannel L s).toLinearMap (MultimodeCoherent.coherentProjector z) -
        vectorProjector (productTensor z L)‖) μ := by
  exact ((occupationChannel L s).toPositiveTracePreservingMap.toContinuousLinearMap.integrable_comp
    (MultimodeCoherent.integrable_coherentProjector μ)).sub
      (integrable_productProjector L μ) |>.norm

/-- Dominated convergence on the full amplitude space, with the actual trace
distance bounded by two. No compact support or Gaussian-tail premise is needed. -/
theorem integral_occupationChannel_error_tendsto {s : ℕ} (μ : Measure (Fin s → ℂ))
    [IsFiniteMeasure μ] : Tendsto (fun L => ∫ z,
      ‖(occupationChannel L s).toLinearMap (MultimodeCoherent.coherentProjector z) -
        vectorProjector (productTensor z L)‖ ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : Fin s → ℂ => (2 : ℝ))
    (fun L => (integrable_occupationChannel_error L μ).aestronglyMeasurable)
    (integrable_const _)
    (fun L => Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        occupationChannel_error_le_two z L))
    (Filter.Eventually.of_forall occupationChannel_error_tendsto)
  simpa using h

theorem occupationChannel_mixture_distance_le {s : ℕ} (L : ℕ)
    (μ : Measure (Fin s → ℂ)) [IsFiniteMeasure μ] :
    ‖(occupationChannel L s).toLinearMap (coherentMixture μ) - productMixture L μ‖ ≤
      ∫ z, ‖(occupationChannel L s).toLinearMap (MultimodeCoherent.coherentProjector z) -
        vectorProjector (productTensor z L)‖ ∂μ := by
  let C := (occupationChannel L s).toPositiveTracePreservingMap.toContinuousLinearMap
  change ‖C (∫ z, MultimodeCoherent.coherentProjector z ∂μ) -
    ∫ z, vectorProjector (productTensor z L) ∂μ‖ ≤ _
  rw [← C.integral_comp_comm (MultimodeCoherent.integrable_coherentProjector μ),
    ← integral_sub (C.integrable_comp (MultimodeCoherent.integrable_coherentProjector μ))
      (integrable_productProjector L μ)]
  exact norm_integral_le_integral_norm _

/-- Actual mixed-state trace-norm approximation after integrating the physical
pure tensors against any finite measure, including the unbounded Gaussian. -/
theorem occupationChannel_mixture_tendsto {s : ℕ} (μ : Measure (Fin s → ℂ))
    [IsFiniteMeasure μ] : Tendsto (fun L =>
      ‖(occupationChannel L s).toLinearMap (coherentMixture μ) - productMixture L μ‖)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun L => occupationChannel_mixture_distance_le L μ)
    (integral_occupationChannel_error_tendsto μ)

end Cloning.GeneralCoherent
