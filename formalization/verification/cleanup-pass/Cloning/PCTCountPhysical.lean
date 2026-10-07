import Cloning.PCTCountAffinity
import Cloning.PCTCountMeasurementMixture

/-! Actual internal maximally mixed PCT fidelity is bounded by the derived count affinity. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace ComplexOrder
open Filter MeasureTheory
namespace Cloning.PCTCount
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PCTCountMeasurement Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def flatState (d : ℕ) : Cloning.MatrixFidelity.State (Fin (d+1)) :=
  diagonalState (flatSpectrum (d+1)) (fun _ ↦ by unfold flatSpectrum; positivity)
    (flatSpectrum_sum _ (by omega))

theorem measuredDensity_flatState (d L : ℕ) (hL : 0<L) :
    measuredDensity d L (tensorState (flatState d) L).1=flatCountDensity d L := by
  funext x
  apply measuredDensity_matrixTensorPower d L hL
  intro i
  simp [flatState, diagonalState]

/-- The internal count measurement detects the variance `2γ-1` of the literal
PCT output. No local Gaussian or measurement premise is assumed. -/
theorem internal_flat_fidelity_eventually_le (d s : ℕ) (hs : 1≤s)
    (hcard : Fintype.card (Fin (d+1) × Fin (d+1))=s+1)
    (t : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun n ↦ ((n+t n : ℕ) : ℝ)/n) atTop (𝓝 γ)) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop,
      (outputState hcard (flatState d) n (t n)).rootFidelity (tensorState (flatState d) (n+t n)) ≤
        Cloning.classicalValue (2*γ-1) (d+1)+ε := by
  obtain ⟨u,hu,hphysical⟩ := Cloning.PCTGlobal.channel_gaussian_product_mixture hs hcard
    (flatState d) t hγ hratio
  have hu' : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))) :=
    hu.trans (canonicalPurification_diagonal (flatSpectrum (d+1))
      (fun _ => by unfold flatSpectrum; positivity))
  let μ := gaussianProductMeasure (fun _ : Fin s ↦ γ-1)
  have hv : 0<γ-1 := by linarith
  letI := gaussianProductMeasure_probability (fun _ : Fin s ↦ hv)
  let n : ℕ → ℕ := fun N ↦ N+t N
  have hn : Tendsto n atTop atTop := tendsto_atTop_mono (fun N ↦ Nat.le_add_right N (t N)) tendsto_id
  let A N := outputState hcard (flatState d) N (t N)
  let B N := tensorState (flatState d) (n N)
  let M N := ∫ z, (frameState u z (n N)).1 ∂μ
  let e N := ‖(A N).1-M N‖
  let a N := ∫ x, Real.sqrt (countMixtureDensity u (γ-1) (n N) x)*Real.sqrt (flatCountDensity d (n N) x)
  have he : Tendsto e atTop (𝓝 0) := hphysical
  have ha : Tendsto a atTop (𝓝 (Cloning.classicalValue (2*γ-1) (d+1))) := by
    have hh := countAffinity_tendsto u hu' (γ-1) hv n hn
    simpa only [show 1+2*(γ-1)=2*γ-1 by ring] using hh
  have hbound : ∀ᶠ N in atTop, (A N).rootFidelity (B N) ≤ Real.sqrt (e N)+a N := by
    filter_upwards [hn.eventually (eventually_gt_atTop 0)] with N hN
    have hB : measuredDensity d (n N) (B N).1=flatCountDensity d (n N) :=
      measuredDensity_flatState d (n N) hN
    have hM : measuredDensity d (n N) (M N)=countMixtureDensity u (γ-1) (n N) := by
      funext x
      exact measuredDensity_frameMixture u (γ-1) hv (n N) hN x
    have hmpos : 0≤(M N).1 := integral_frameState_nonneg u (n N) μ
    have hc := measuredDensity_l1_contraction d (n N) hN (A N).1 (M N) (A N).2 hmpos
    rw [hM] at hc
    have hb := rootFidelity_le_measuredDensity_affinity d (n N) hN (A N) (B N)
    rw [hB] at hb
    have hp := density_affinity_l1_bound volume (measuredDensity d (n N) (A N).1)
      (countMixtureDensity u (γ-1) (n N)) (flatCountDensity d (n N))
      (integrable_measuredDensity d (n N) hN (A N).1)
      (integrable_countMixtureDensity u (γ-1) hv (n N) hN)
      (CountMultinomial.integrable_density d (n N) hN _ _ _)
      (measuredDensity_nonneg d (n N) hN (A N).1 (A N).2)
      (countMixtureDensity_nonneg u (γ-1) (n N))
      (CountMultinomial.density_nonneg d (n N) _ _ _)
      (CountMultinomial.integral_density d (n N) hN _ _ _)
    have hple := (le_abs_self _).trans (hp.trans (Real.sqrt_le_sqrt hc))
    change (∫ x, Real.sqrt (measuredDensity d (n N) (A N).1 x)*Real.sqrt (flatCountDensity d (n N) x))-a N ≤ Real.sqrt (e N) at hple
    linarith
  have hh := he.sqrt.add ha
  simp only [Real.sqrt_zero, zero_add] at hh
  intro ε hε
  filter_upwards [hbound, hh.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))] with N hb ht
  exact hb.trans ht.le

end Cloning.PCTCount
