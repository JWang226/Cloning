import Cloning.PCTProjectorPurityEnvelopePhysical
import Cloning.PCTProjectorPurityEnvelopeExpansion
import Cloning.PCTProjectorPurityPhysical
import Cloning.PCTWernerLower

/-! The actual fixed projector PCT channel has the rank-boundary small-gain
coefficient, uniformly over all literal Grassmann projectors. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Filter
namespace Cloning.PCTProjectorPurity
open Cloning.PCT Cloning.PCTRankAdapted Cloning.PCTPhysicalState
open Cloning.PhysicalFlatGrassmann Cloning.InfiniteTraceClass Cloning.Hybrid
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- This adapter includes the one-dimensional internal system, where the
actual internal fidelity is exactly one at every finite sample size. -/
theorem internal_flat_squared_error_all_ranks (d : ℕ) (t : ℕ→ℕ)
    (δ : ℝ) (hδ : 0<δ) (hδr : δ<1/(2*((d+1:ℕ):ℝ)))
    (hgain : Tendsto (fun n=>((n+t n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) :
    ∀ε>0,∀ᶠ (n : ℕ) in atTop,
      1-((PCTPhysicalState.outputState (flat_internal_register_card d) (flatInternalState d)
        n (t n)).rootFidelity (tensorState (flatInternalState d) (n+t n)))^2≤
        internalError (d*(d+2)) δ+ε := by
  by_cases hd : d=0
  · subst d
    intro ε hε
    apply Eventually.of_forall
    intro n
    have hl := outputState_fidelity_lower (flat_internal_register_card 0) (flatInternalState 0) n (t n)
    have hu := internal_fidelity_le_one (flat_internal_register_card 0) (flatInternalState 0) n (t n)
    have hf : (PCTPhysicalState.outputState (flat_internal_register_card 0) (flatInternalState 0)
        n (t n)).rootFidelity (tensorState (flatInternalState 0) (n+t n))=1 := by
      apply le_antisymm hu
      simpa [wernerScale] using hl
    simp only [hf,one_pow,sub_self,Nat.zero_mul,internalError,Nat.cast_zero,zero_div,neg_zero,
      Real.rpow_zero,sub_self,zero_add]
    exact hε.le
  · simpa only [internalError,neg_div] using
      internal_flat_squared_error_eventually_le d (d*(d+2)) (by omega) (by
          have hdpos : 1≤d := by omega
          exact le_trans (by omega : 1≤d) (Nat.le_mul_of_pos_right d (by omega)))
        (flat_internal_register_card d) t δ hδ hδr hgain

/-- Unconditional asymptotic envelopes for the actual state-independent
rank-adapted channel; no internal purity or Gaussian approximation premise. -/
theorem physical_error_envelopes (d k : ℕ) (t : ℕ→ℕ)
    (δ : ℝ) (hδ : 0<δ) (hδr : δ<1/(2*((d+1:ℕ):ℝ)))
    (hgain : Tendsto (fun n=>((n+t n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) :
    ∀ε>0,∀ᶠ (n : ℕ) in atTop,∀P : Projector (d+1) k,
      lowerEnvelope ((d+1)*k) δ-ε≤1-(Cloning.PhysicalFlatPCT.fidelity d k P n (t n))^2 ∧
      1-(Cloning.PhysicalFlatPCT.fidelity d k P n (t n))^2≤
        upperEnvelope ((d+1)*k) (d*(d+2)) δ+ε :=
  physical_error_envelopes_of_internal_bound d k t δ hδ hgain
    (internal_flat_squared_error_all_ranks d t δ hδ hδr hgain)

/-- The coefficient of small additional-copy gain is exactly r*(ambient-r),
after the large-sample limit, uniformly over the unknown projector. -/
theorem physical_small_gain_coefficient (d k : ℕ) (t : ℝ→ℕ→ℕ)
    (hgain : ∀δ,0<δ→δ<1/(2*((d+1:ℕ):ℝ))→
      Tendsto (fun n=>((n+t δ n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) :
    ∀η>0,∀ᶠ δ in 𝓝[>] (0:ℝ),∀ᶠ (n : ℕ) in atTop,∀P : Projector (d+1) k,
      |(1-(Cloning.PhysicalFlatPCT.fidelity d k P n (t δ n))^2)/δ-
        (((d+1)*k:ℕ):ℝ)|≤η := by
  apply error_envelopes_first_order ((d+1)*k) (d*(d+2))
    (1/(2*((d+1:ℕ):ℝ))) (by positivity)
    (fun δ n P=>1-(Cloning.PhysicalFlatPCT.fidelity d k P n (t δ n))^2)
  intro δ hd hsmall
  exact physical_error_envelopes d k (t δ) δ hd hsmall (hgain δ hd hsmall)

end Cloning.PCTProjectorPurity
