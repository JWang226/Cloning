import Cloning.PCTPhysicalFidelity
import Cloning.PCTUnitaryTransportChannels

/-! Physical PCT fidelity on the entire unitary orbit of every simple
full-rank spectrum. The only analytic hypothesis is genuine compact-window
mixed LAN at the diagonal base. The physical protocol is unchanged. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.Hybrid
namespace Cloning.PCTPhysicalFidelity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.PCTJointGaussianWhitening Cloning.PCTPurificationChannel
open Cloning.MultimodeCoherent Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k d s : ℕ}

theorem mapped_error_tendsto
    (M : ∀ L, QuantumChannel (Register (Fin L → Fin (k+1))) (Register (Fin L → Fin (k+1))))
    (X Y : ∀ L, TraceClass (Register (Fin L → Fin (k+1))))
    (h : Tendsto (fun L => ‖X L - Y L‖) atTop (𝓝 0)) :
    Tendsto (fun L => ‖(M L).toLinearMap (X L) - (M L).toLinearMap (Y L)‖)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun L => norm_nonneg _) _ (by simpa using h.const_mul 2)
  intro L
  rw [← map_sub]
  exact (M L).toPositiveTracePreservingMap.norm_map_le_two_mul _

def rotatedForward {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e) (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ)) (L : ℕ) :=
  (lan.forward L).compQuantum (unitaryChannel (tensorUnitary (star U) L))

def rotatedReverse {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e) (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ)) (L : ℕ) :=
  postQuantum (unitaryChannel (tensorUnitary U L)) (lan.reverse L)

theorem CompactWindowLAN.rotated_seed_limits
    {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e) (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ)) :
    Tendsto (fun L => ‖(rotatedForward lan U L).map
      (tensorState (conjugatedState (baseState p) U) L).1 - (reference p e).1‖) atTop (𝓝 0) ∧
    Tendsto (fun L => ‖(rotatedReverse lan U L).map (reference p e).1 -
      (tensorState (conjugatedState (baseState p) U) L).1‖) atTop (𝓝 0) := by
  constructor
  · simpa only [rotatedForward, QuantumToHybrid.compQuantum_apply, tensorState_conjugated_inverse]
      using lan.seed_limits.1
  · have h := mapped_error_tendsto (fun L => unitaryChannel (tensorUnitary U L))
      (fun L => (lan.reverse L).map (reference p e).1)
      (fun L => (tensorState (baseState p) L).1) lan.seed_limits.2
    simpa only [rotatedReverse, postQuantum_apply, tensorState_conjugated] using h

theorem CompactWindowLAN.rotated_frame_limits
    {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e) (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ))
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (k+1) × Fin (k+1))))
    (hu : transportFrame u (star U) 0 = coefficientVector (schmidtCoefficients p.eigenvalue))
    (z : Fin s → ℂ) :
    Tendsto (fun L => ‖(rotatedForward lan U L).map (frameState u z L).1 -
      (frameModel p b e (transportFrame u (star U)) z).1‖) atTop (𝓝 0) ∧
    Tendsto (fun L => ‖(rotatedReverse lan U L).map
      (frameModel p b e (transportFrame u (star U)) z).1 - (frameState u z L).1‖)
      atTop (𝓝 0) := by
  have h := lan.frame_limits (transportFrame u (star U)) hu z
  constructor
  · simpa only [rotatedForward, QuantumToHybrid.compQuantum_apply, frameState_transport] using h.1
  · have hm := mapped_error_tendsto (fun L => unitaryChannel (tensorUnitary U L))
      (fun L => (lan.reverse L).map (frameModel p b e (transportFrame u (star U)) z).1)
      (fun L => (frameState (transportFrame u (star U)) z L).1) h.2
    have he (L : ℕ) : (unitaryChannel (tensorUnitary U L)).toLinearMap
        (frameState (transportFrame u (star U)) z L).1 = (frameState u z L).1 := by
      simpa only [star_star] using frameState_transport_inverse u (star U) z L
    simpa only [rotatedReverse, postQuantum_apply, he] using hm

/-- Full unitary-orbit physical PCT fidelity, conditional solely on the
explicit genuine compact-window mixed-LAN property at the simple spectrum. -/
theorem physical_pct_fidelity_unitary_of_compactWindowLAN
    (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin d ≃ PairIndex (k+1))
    (lan : CompactWindowLAN p b e) (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ))
    (hs : 1 ≤ s) (hcard : Fintype.card (Fin (k+1) × Fin (k+1)) = s+1)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n =>
      (outputState hcard (conjugatedState (baseState p) U) n (r n)).rootFidelity
      (tensorState (conjugatedState (baseState p) U) (n+r n))) atTop (𝓝 (pctValue γ p)) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => sub_pos.mpr hγ)
  obtain ⟨u, hu, hphysical⟩ := Cloning.PCTGlobal.channel_gaussian_product_mixture
    hs hcard (conjugatedState (baseState p) U) r hγ hr
  let v := transportFrame u (star U)
  have hv : v 0 = coefficientVector (schmidtCoefficients p.eigenvalue) :=
    (transportFrame_canonical_zero u (baseState p) U hu).trans
      (canonicalPurification_diagonal p.eigenvalue (fun i => (p.positive i).le))
  have hm : Tendsto (fun n => n+r n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n (r n)) tendsto_id
  have hseed := lan.rotated_seed_limits U
  have hforward : ∀ᵐ z ∂gaussianProductMeasure (fun _ : Fin s => γ-1),
      Tendsto (fun n => ‖(rotatedForward lan U (n+r n)).map (frameState u z (n+r n)).1 -
        (frameModel p b e v z).1‖) atTop (𝓝 0) :=
    Eventually.of_forall (fun z => (lan.rotated_frame_limits U u hv z).1.comp hm)
  have hreverse : ∀ᵐ z ∂gaussianProductMeasure (fun _ : Fin s => γ-1),
      Tendsto (fun n => ‖(rotatedReverse lan U (n+r n)).map (frameModel p b e v z).1 -
        (frameState u z (n+r n)).1‖) atTop (𝓝 0) :=
    Eventually.of_forall (fun z => (lan.rotated_frame_limits U u hv z).2.comp hm)
  have hf := Cloning.MixedLANTransfer.fidelity_tendsto_of_mixed_mixture
    (fun n => rotatedForward lan U (n+r n)) (fun n => rotatedReverse lan U (n+r n))
    (fun n => tensorState (conjugatedState (baseState p) U) (n+r n))
    (fun n => outputState hcard (conjugatedState (baseState p) U) n (r n))
    (reference p e) (comparison p e γ hγ)
    (fun n z => frameState u z (n+r n)) (frameModel p b e v)
    (fun n => norm_tensorState _ _) (fun n => norm_outputState _ _ _ _)
    (norm_reference p e) (norm_comparison p e γ hγ)
    (fun n z => norm_frameState _ _ _) (norm_frameModel p b e v)
    (fun n => integrable_frameState u (n+r n) _) (integrable_frameModel p b e v _)
    (frameModel_integral p v hv b hb e γ hγ) hphysical
    (hseed.1.comp hm) (hseed.2.comp hm) hforward hreverse
  simpa only [PositiveTraceClass.rootFidelity_comm, reference_comparison_fidelity] using hf

/-- The same endpoint for any density matrix equipped with its actual unitary
diagonalization at the stated simple spectrum. -/
theorem physical_pct_fidelity_of_diagonalization
    (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = sqrtSpectrum p.eigenvalue) (e : Fin d ≃ PairIndex (k+1))
    (lan : CompactWindowLAN p b e) (ρ : Cloning.MatrixFidelity.State (Fin (k+1)))
    (U : unitary (Matrix (Fin (k+1)) (Fin (k+1)) ℂ))
    (hρ : ρ.matrix = (U : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) *
      Matrix.diagonal (fun i => (p.eigenvalue i : ℂ)) * (U : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)ᴴ)
    (hs : 1 ≤ s) (hcard : Fintype.card (Fin (k+1) × Fin (k+1)) = s+1)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (outputState hcard ρ n (r n)).rootFidelity
      (tensorState ρ (n+r n))) atTop (𝓝 (pctValue γ p)) := by
  have he : ρ = conjugatedState (baseState p) U := by
    cases ρ
    congr
  subst ρ
  exact physical_pct_fidelity_unitary_of_compactWindowLAN p b hb e lan U hs hcard r γ hγ hr

end Cloning.PCTPhysicalFidelity
