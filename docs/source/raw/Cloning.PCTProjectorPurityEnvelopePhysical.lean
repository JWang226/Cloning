import Cloning.PCTProjectorPurityEnvelope
import Cloning.PhysicalFlatPCTTheorem

/-! Transfer of an explicit internal squared-error estimate to the fixed
physical rank-adapted PCT channel, uniformly over all Grassmann projectors. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTRankAdapted Cloning.PCTPhysicalState
open Cloning.PhysicalFlatGrassmann Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The exact rank boundary determines the support mass limit. -/
theorem flat_supportFactor_tendsto (d k : ℕ) (t : ℕ→ℕ) (δ : ℝ) (hδ : 0<δ)
    (hgain : Tendsto (fun n=>((n+t n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) :
    Tendsto (fun n=>supportFactor n (n+t n) (d*(d+2)) (flatPurificationDimension d k))
      atTop (𝓝 (supportLimit ((d+1)*k) δ)) := by
  have hg : 0<1+δ := by linarith
  have h := supportFactor_tendsto (fun n=>n+t n) (by linarith : 1<1+δ)
    hgain (d*(d+2)) (flatPurificationDimension d k)
  have he : (1/(1+δ))^(flatPurificationDimension d k)/(1/(1+δ))^(d*(d+2))=
      supportLimit ((d+1)*k) δ := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_sub (one_div_pos.mpr hg),
      one_div,Real.inv_rpow hg.le,← Real.rpow_neg hg.le]
    unfold supportLimit
    congr 1
    unfold flatPurificationDimension
    push_cast
    ring
  exact he ▸ h

/-- This is an intermediate implication. Its sole unclosed analytic input
is the stated bound on the actual internal PCT squared fidelity. -/
theorem physical_error_envelopes_of_internal_bound (d k : ℕ) (t : ℕ→ℕ)
    (δ : ℝ) (hδ : 0<δ)
    (hgain : Tendsto (fun n=>((n+t n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ)))
    (hint : ∀ε>0,∀ᶠ (n : ℕ) in atTop,
      1-((PCTPhysicalState.outputState (flat_internal_register_card d) (flatInternalState d)
        n (t n)).rootFidelity (tensorState (flatInternalState d) (n+t n)))^2≤
        internalError (d*(d+2)) δ+ε) :
    ∀ε>0,∀ᶠ (n : ℕ) in atTop,∀P : Projector (d+1) k,
      lowerEnvelope ((d+1)*k) δ-ε≤1-(Cloning.PhysicalFlatPCT.fidelity d k P n (t n))^2 ∧
      1-(Cloning.PhysicalFlatPCT.fidelity d k P n (t n))^2≤
        upperEnvelope ((d+1)*k) (d*(d+2)) δ+ε := by
  let s := fun n=>supportFactor n (n+t n) (d*(d+2)) (flatPurificationDimension d k)
  let u := fun n=>(PCTPhysicalState.outputState (flat_internal_register_card d)
    (flatInternalState d) n (t n)).rootFidelity (tensorState (flatInternalState d) (n+t n))
  have hs : ∀n,0≤s n := fun n=>(supportFactor_pos _ _ _ _).le
  have hu : ∀n,0≤u n ∧ u n≤1 := fun n=>
    ⟨PositiveTraceClass.rootFidelity_nonneg _ _,
      internal_fidelity_le_one (flat_internal_register_card d) (flatInternalState d) n (t n)⟩
  have h := eventually_supported_error_envelopes s u (supportLimit ((d+1)*k) δ)
    (internalError (d*(d+2)) δ) (supportLimit_nonneg _ _ hδ.le)
    (supportLimit_le_one _ _ hδ.le) hs hu (flat_supportFactor_tendsto d k t δ hδ hgain) hint
  intro ε hε
  filter_upwards [h ε hε] with n hn P
  rw [Cloning.PhysicalFlatPCT.fidelity_eq_supportFactor,mul_pow,
    Real.sq_sqrt (supportFactor_pos _ _ _ _).le]
  exact hn

end Cloning.PCTProjectorPurity
