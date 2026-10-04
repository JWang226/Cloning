import Cloning.PCTPhysicalFidelityFrame

/-! Exact physical PCT fidelity at a simple diagonal base, conditional only
on genuine compact-window mixed-state LAN. Every mixture, normalization,
integrability, chart and scaling input to the fidelity transfer is proved. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.Hybrid
namespace Cloning.PCTPhysicalFidelity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTLocalChart Cloning.PCTJointGaussianWhitening Cloning.PCTPhysicalState
open Cloning.PCTHybridMixture Cloning.PCTPurificationChannel
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k d s : ℕ}

def comparison (p : SimpleSpectrum (k+1)) (e : Fin d ≃ PairIndex (k+1))
    (γ : ℝ) (hγ : 1 < γ) : HybridPositive k d :=
  pctGaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num) γ hγ
    (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))

@[simp] theorem norm_comparison (p : SimpleSpectrum (k+1)) (e : Fin d ≃ PairIndex (k+1))
    (γ : ℝ) (hγ : 1 < γ) : ‖(comparison p e γ hγ).1‖ = 1 :=
  norm_pctGaussianThermalPositive _ _ _ _ _ _ _

theorem reference_comparison_fidelity (p : SimpleSpectrum (k+1)) (e : Fin d ≃ PairIndex (k+1))
    (γ : ℝ) (hγ : 1 < γ) :
    (reference p e).rootFidelity (comparison p e γ hγ) = pctValue γ p := by
  rw [PositiveL1.rootFidelity_comm]
  exact pctGaussianThermalPositive_rootFidelity_eq_pctValue _ _ γ hγ p e

theorem frameModel_integral (p : SimpleSpectrum (k+1))
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (k+1) × Fin (k+1))))
    (hu : u 0 = coefficientVector (schmidtCoefficients p.eigenvalue))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin d ≃ PairIndex (k+1))
    (γ : ℝ) (hγ : 1 < γ) :
    (comparison p e γ hγ).1 = ∫ z, (frameModel p b e u z).1
      ∂gaussianProductMeasure (fun _ : Fin s => γ-1) := by
  symm
  exact tangent_hybrid_average_eq_pctGaussianThermalPositive u p.eigenvalue p.positive hu
    (fun i j hij => sub_pos.mpr (p.strictAnti hij)) b hb e γ hγ

/-- The actual state-independent physical channel has the manuscript's PCT
root-fidelity limit if the explicitly defined genuine mixed-LAN property is
proved. No local-chart or pointwise-mixture approximation remains a premise. -/
theorem physical_pct_fidelity_of_compactWindowLAN
    (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin d ≃ PairIndex (k+1))
    (lan : CompactWindowLAN p b e) (hs : 1 ≤ s)
    (hcard : Fintype.card (Fin (k+1) × Fin (k+1)) = s+1)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (outputState hcard (baseState p) n (r n)).rootFidelity
      (tensorState (baseState p) (n+r n))) atTop (𝓝 (pctValue γ p)) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => sub_pos.mpr hγ)
  obtain ⟨u, hu, hphysical⟩ := Cloning.PCTGlobal.channel_gaussian_product_mixture
    hs hcard (baseState p) r hγ hr
  have hu' : u 0 = coefficientVector (schmidtCoefficients p.eigenvalue) :=
    hu.trans (canonicalPurification_diagonal p.eigenvalue (fun i => (p.positive i).le))
  have hm : Tendsto (fun n => n+r n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n (r n)) tendsto_id
  have hseed := lan.seed_limits
  have hforward : ∀ᵐ z ∂gaussianProductMeasure (fun _ : Fin s => γ-1),
      Tendsto (fun n => ‖(lan.forward (n+r n)).map (frameState u z (n+r n)).1 -
        (frameModel p b e u z).1‖) atTop (𝓝 0) :=
    Eventually.of_forall (fun z => (lan.frame_limits u hu' z).1.comp hm)
  have hreverse : ∀ᵐ z ∂gaussianProductMeasure (fun _ : Fin s => γ-1),
      Tendsto (fun n => ‖(lan.reverse (n+r n)).map (frameModel p b e u z).1 -
        (frameState u z (n+r n)).1‖) atTop (𝓝 0) :=
    Eventually.of_forall (fun z => (lan.frame_limits u hu' z).2.comp hm)
  have hf := Cloning.MixedLANTransfer.fidelity_tendsto_of_mixed_mixture
    (fun n => lan.forward (n+r n)) (fun n => lan.reverse (n+r n))
    (fun n => tensorState (baseState p) (n+r n))
    (fun n => outputState hcard (baseState p) n (r n))
    (reference p e) (comparison p e γ hγ)
    (fun n z => frameState u z (n+r n)) (frameModel p b e u)
    (fun n => norm_tensorState _ _) (fun n => norm_outputState _ _ _ _)
    (norm_reference p e) (norm_comparison p e γ hγ)
    (fun n z => norm_frameState _ _ _) (norm_frameModel p b e u)
    (fun n => integrable_frameState u (n+r n) _) (integrable_frameModel p b e u _)
    (frameModel_integral p u hu' b hb e γ hγ) hphysical
    (hseed.1.comp hm) (hseed.2.comp hm) hforward hreverse
  simpa only [PositiveTraceClass.rootFidelity_comm, reference_comparison_fidelity] using hf

end Cloning.PCTPhysicalFidelity
