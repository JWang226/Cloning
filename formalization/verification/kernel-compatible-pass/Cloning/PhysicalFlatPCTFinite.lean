import Cloning.PCTWernerLower
import Cloning.SampleRatioFinite
import Cloning.PhysicalFlatPCTTheorem
import Cloning.PCTPrescribedRank

/-! Finite-copy PCT squared-fidelity certification for every literal flat
projector and for the actual prescribed state-independent channel. -/
noncomputable section
open scoped ComplexOrder Topology
namespace Cloning.PhysicalFlatPCT
open Cloning.PCTRankAdapted Cloning.PCTPhysicalState Cloning.PhysicalFlatGrassmann
set_option backward.isDefEq.respectTransparency false

theorem fidelity_lower (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) :
    Real.sqrt (wernerScale n (n+t) (flatPurificationDimension d k)) ≤ fidelity d k P n t := by
  rw [fidelity_eq_supportFactor]
  have h := mul_le_mul_of_nonneg_left
    (outputState_fidelity_lower (flat_internal_register_card d) (flatInternalState d) n t)
    (Real.sqrt_nonneg (supportFactor n (n+t) (d*(d+2)) (flatPurificationDimension d k)))
  rw [← Real.sqrt_mul (supportFactor_pos n (n+t) (d*(d+2)) (flatPurificationDimension d k)).le] at h
  simpa only [supportFactor,div_mul_cancel₀ _ (wernerScale_pos n (n+t) (d*(d+2))).ne'] using h

theorem fidelity_sq_lower (d k : ℕ) (P : Projector (d+1) k) (n t : ℕ) :
    wernerScale n (n+t) (flatPurificationDimension d k) ≤ fidelity d k P n t^2 := by
  have h := fidelity_lower d k P n t
  have hs := Real.sq_sqrt (wernerScale_pos n (n+t) (flatPurificationDimension d k)).le
  nlinarith [Real.sqrt_nonneg (wernerScale n (n+t) (flatPurificationDimension d k)),
    fidelity_nonneg d k P n t]

theorem fidelity_sq_ge_target (d k : ℕ) (P : Projector (d+1) k) (N M : ℕ)
    (hN : 0<N) (hM : 0<M) (ha : 0<flatPurificationDimension d k)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (hR : SampleRatio.threshold (flatPurificationDimension d k) ε ≤ (N:ℝ)/M) :
    1-ε ≤ fidelity d k P N M^2 :=
  (SampleRatio.wernerScale_ge_target N M (flatPurificationDimension d k)
    hN hM ha hε hε1 hR).trans (fidelity_sq_lower d k P N M)

theorem prescribed_fidelity_sq_ge_target (d k : ℕ) (P : Projector (d+1) k) (N M : ℕ)
    (hN : 0<N) (hM : 0<M) (ha : 0<flatPurificationDimension d k)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (hR : SampleRatio.threshold (flatPurificationDimension d k) ε ≤ (N:ℝ)/M) :
    1-ε ≤ PCTPrescribed.rankFidelity d k P N (N+M)^2 := by
  have he : PCTPrescribed.rankFidelity d k P N (N+M)=fidelity d k P N M := by
    unfold PCTPrescribed.rankFidelity PCTPrescribed.rankChannel
    rw [PCTPrescribed.extendChannel_add (channel d k) N M hM]
    rfl
  rw [he]
  exact fidelity_sq_ge_target d k P N M hN hM ha hε hε1 hR

end Cloning.PhysicalFlatPCT
