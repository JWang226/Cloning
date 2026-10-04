import Cloning.PCTProjectorPurityLimit
import Cloning.PCTPurityFidelityPhysical

/-! The actual physical internal PCT output obeys the small-error purity
bound. The Gaussian mixture approximation is transferred through the proved
trace-norm continuity of root fidelity. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder InnerProductSpace
open Filter MeasureTheory
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPhysicalState
open Cloning.PCTLocalChart Cloning.PCTGaussianCovariance Cloning.YoungGeneral
open Cloning.MultimodeCoherentGaussianMixture Cloning.Hybrid Cloning.PCTRankAdapted
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 250000

/-- Exact scaled purity of the literal positive tensor mixture. -/
theorem frameMixture_scaled_purity_tendsto (d s : ℕ) (hd : 1≤d)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin (d+1)×Fin (d+1))))
    (hu : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))))
    {δ : ℝ} (hδ : 0<δ) (hδr : δ<1/(2*((d+1:ℕ):ℝ))) :
    Tendsto (fun L : ℕ => ((d+1:ℕ):ℝ)^L*(Matrix.trace
      (Cloning.PCTPurity.frameMixtureMatrix u (gaussianProductMeasure (fun _ : Fin s => δ)) L*
       Cloning.PCTPurity.frameMixtureMatrix u (gaussianProductMeasure (fun _ : Fin s => δ)) L)).re)
      atTop (𝓝 ((1-4*δ^2)^(-(s:ℝ)/2))) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hδ)
  simpa only [Cloning.PCTPurity.frameMixtureMatrix_scaled_purity,particle] using
    particle_purity_iterated_integral_tendsto (by omega) u hu hδ hδr

/-- The appendix's internal squared-error bound for the literal full-environment
PCT output. The only assumptions are rank, variance and output-size scaling. -/
theorem internal_flat_squared_error_eventually_le (d s : ℕ) (hd : 1≤d) (hs : 1≤s)
    (hcard : Fintype.card (Fin (d+1)×Fin (d+1))=s+1)
    (t : ℕ→ℕ) (δ : ℝ) (hδ : 0<δ) (hδr : δ<1/(2*((d+1:ℕ):ℝ)))
    (hratio : Tendsto (fun n => ((n+t n:ℕ):ℝ)/n) atTop (𝓝 (1+δ))) :
    ∀ε : ℝ,0<ε → ∀ᶠ n in atTop,
      1-((outputState hcard (flatInternalState d) n (t n)).rootFidelity
        (tensorState (flatInternalState d) (n+t n)))^2≤
      ((1-4*δ^2)^(-(s:ℝ)/2)-1)+ε := by
  obtain ⟨u,hu,hphysical⟩ := Cloning.PCTGlobal.channel_gaussian_product_mixture hs hcard
    (flatInternalState d) t (by linarith : 1<1+δ) hratio
  have hu' : u 0=coefficientVector (schmidtCoefficients (flatSpectrum (d+1))) :=
    hu.trans (canonicalPurification_diagonal (flatSpectrum (d+1))
      (fun _ => by unfold flatSpectrum; positivity))
  let μ := gaussianProductMeasure (fun _ : Fin s => δ)
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hδ)
  let n : ℕ→ℕ := fun N => N+t N
  have hn : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right N (t N)) tendsto_id
  let A N := outputState hcard (flatInternalState d) N (t N)
  let B N := tensorState (flatInternalState d) (n N)
  let M N := Cloning.PCTPurity.frameMixture u μ (n N)
  let e N := ‖(A N).1-(M N).1‖
  let J L := ∫z,∫w,(((d+1:ℕ):ℝ)*(Matrix.trace (particle u z L*particle u w L)).re)^L ∂μ ∂μ
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [show 1+δ-1=δ by ring] using hphysical
  have hJ : Tendsto (fun N => J (n N)) atTop (𝓝 ((1-4*δ^2)^(-(s:ℝ)/2))) :=
    (particle_purity_iterated_integral_tendsto (by omega) u hu' hδ hδr).comp hn
  have hb (N : ℕ) : 1-((A N).rootFidelity (B N))^2≤J (n N)-1+2*Real.sqrt (e N) := by
    have hB : ‖(B N).1‖=1 := norm_tensorState _ _
    have hA : ‖(A N).1‖=1 := norm_outputState _ _ _ _
    have hM : ‖(M N).1‖=1 := Cloning.PCTCountMeasurement.norm_integral_frameState u (n N) μ
    have hcont := PositiveTraceClass.rootFidelity_continuity (A N) (B N) (M N) (B N)
    simp only [hB,sub_self,norm_zero,Real.sqrt_zero,Real.sqrt_one,mul_one,zero_mul,add_zero] at hcont
    have ha := (A N).rootFidelity_le_sqrt (B N)
    have hm := (M N).rootFidelity_le_sqrt (B N)
    simp only [hA,hM,hB,Real.sqrt_one,one_mul] at ha hm
    have hsub : (M N).rootFidelity (B N)-(A N).rootFidelity (B N)≤Real.sqrt (e N) := by
      have hh := (abs_le.mp hcont).1
      change -Real.sqrt (e N)≤(A N).rootFidelity (B N)-(M N).rootFidelity (B N) at hh
      linarith
    have hsum : (A N).rootFidelity (B N)+(M N).rootFidelity (B N)≤2 := by linarith
    have hsq := mul_le_mul hsub hsum
      (add_nonneg ((A N).rootFidelity_nonneg (B N)) ((M N).rootFidelity_nonneg (B N)))
      (Real.sqrt_nonneg (e N))
    have hfinite := Cloning.PCTPurity.frameMixture_fidelity_purity_bound u μ (n N)
    change 1-((M N).rootFidelity (B N))^2≤J (n N)-1 at hfinite
    nlinarith
  have hlim := (hJ.sub_const 1).add (he.sqrt.const_mul 2)
  simp only [Real.sqrt_zero,mul_zero,add_zero] at hlim
  intro ε hε
  filter_upwards [hlim.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))] with N hN
  exact (hb N).trans hN.le

end Cloning.PCTProjectorPurity
