import Cloning.PCTPrescribedRank
import Cloning.PCTRankPurificationGeneralFinite

/-! The prescribed PCT channel has the manuscript's finite guarantee on the
entire rank-bounded state family, not only on normalized projectors. Its rank
bound is d+1 and its system dimension is d+1+k. All sample sizes, including
restriction and zero additional copies, use the same prescribed channel. -/
noncomputable section
open scoped Topology Matrix
open Filter
namespace Cloning.PCTPrescribed
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted
open Cloning.PCTRankPurification Cloning.TensorCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance guaranteeAmbientNonempty (d k : ℕ) : Nonempty (Fin (d+1+k)) :=
  ⟨⟨0,by omega⟩⟩

/-- The mode count is exactly rank bound times system dimension, minus one. -/
theorem flatPurificationDimension_eq_rank_times_dimension (d k : ℕ) :
    flatPurificationDimension d k=(d+1)*(d+1+k)-1 := by
  unfold flatPurificationDimension
  have h : d*(d+2)+k*(d+1)+1=(d+1)*(d+1+k) := by ring
  omega

/-- The concrete fixed coordinate-fallback channel has the arbitrary-state
lower bound, with no purification or support witness supplied by the caller. -/
theorem physical_rank_statePayoff_lower (d k n t : ℕ)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1+k)))
    (hrank : ρ.matrix.rank≤d+1) :
    Real.sqrt (wernerScale n (n+t) (flatPurificationDimension d k)) ≤
      statePayoff n (n+t) (PhysicalFlatPCT.channel d k n t) ρ := by
  exact channel_rank_le_fidelity_lower k n t (flat_ambient_register_card d k)
    (fun _=>⟨0,by omega⟩,fun _=>⟨0,by omega⟩) ρ hrank

/-- The prescribed channel's guarantee is valid at every n≤m, including n=m. -/
theorem rankChannel_statePayoff_lower (d k n m : ℕ) (hnm : n≤m)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1+k)))
    (hrank : ρ.matrix.rank≤d+1) :
    Real.sqrt (wernerScale n m (flatPurificationDimension d k)) ≤
      statePayoff n m (rankChannel d k n m) ρ := by
  rcases hnm.eq_or_lt with he|hlt
  · subst m
    rw [show statePayoff n n (rankChannel d k n n) ρ=1 from
      extendChannel_payoff_of_le (PhysicalFlatPCT.channel d k) n n le_rfl ρ]
    have hc : (Nat.choose (n+flatPurificationDimension d k) (flatPurificationDimension d k):ℝ)≠0 :=
      by exact_mod_cast (Nat.choose_pos (by omega : flatPurificationDimension d k≤n+flatPurificationDimension d k)).ne'
    simp [wernerScale,hc]
  · have h := physical_rank_statePayoff_lower d k n (m-n) ρ hrank
    rw [← extendChannel_payoff_of_gt (PhysicalFlatPCT.channel d k) n m hlt ρ] at h
    simpa only [Nat.add_sub_of_le hnm,rankChannel] using h

theorem rankChannel_statePayoff_sq_lower (d k n m : ℕ) (hnm : n≤m)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1+k)))
    (hrank : ρ.matrix.rank≤d+1) :
    wernerScale n m (flatPurificationDimension d k) ≤
      statePayoff n m (rankChannel d k n m) ρ^2 := by
  have h := rankChannel_statePayoff_lower d k n m hnm ρ hrank
  have hs := Real.sq_sqrt (wernerScale_pos n m (flatPurificationDimension d k)).le
  have hp := statePayoff_nonneg n m (rankChannel d k n m) ρ
  nlinarith [Real.sqrt_nonneg (wernerScale n m (flatPurificationDimension d k))]

/-- One explicit finite sample threshold works simultaneously for all
density matrices of rank at most d+1, irrespective of spectrum or support. -/
theorem rankChannel_uniform_sample_guarantee (d k N M : ℕ)
    (hN : 0<N) (hM : 0<M) (hD : 1<(d+1)*(d+1+k))
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (hR : SampleRatio.threshold (((d+1)*(d+1+k)-1:ℕ):ℝ) ε≤(N:ℝ)/M) :
    ∀ρ : Cloning.MatrixFidelity.State (Fin (d+1+k)),ρ.matrix.rank≤d+1 →
      1-ε≤statePayoff N (N+M) (rankChannel d k N (N+M)) ρ^2 := by
  intro ρ hrank
  have hs : 0<flatPurificationDimension d k := by
    rw [flatPurificationDimension_eq_rank_times_dimension]
    omega
  have hR' : SampleRatio.threshold (flatPurificationDimension d k) ε≤(N:ℝ)/M := by
    simpa only [flatPurificationDimension_eq_rank_times_dimension] using hR
  exact (SampleRatio.wernerScale_ge_target N M _ hN hM hs hε hε1 hR').trans
    (rankChannel_statePayoff_sq_lower d k N (N+M) (Nat.le_add_right N M) ρ hrank)

/-- The binomial root bound has the literal exponent -(rD-1)/2. -/
theorem rank_guarantee_tendsto (d k : ℕ) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n=>(m n:ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n=>Real.sqrt (wernerScale n (m n) (flatPurificationDimension d k)))
      atTop (𝓝 (γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2))) := by
  have h := (wernerScale_tendsto m hγ hgain (flatPurificationDimension d k)).sqrt
  have hg : 0<γ := by linarith
  have he : Real.sqrt ((1/γ)^flatPurificationDimension d k)=
      γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (one_div_pos.mpr hg).le,
      one_div,Real.inv_rpow hg.le,← Real.rpow_neg hg.le,
      flatPurificationDimension_eq_rank_times_dimension]
    congr 1
    ring
  exact he ▸ h

/-- The lower guarantee is uniform even when an adversary changes the
input spectrum, support and rank with the sample size. -/
theorem rankChannel_uniform_asymptotic_lower (d k : ℕ)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n=>(m n:ℝ)/n) atTop (𝓝 γ))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ρ : Cloning.MatrixFidelity.State (Fin (d+1+k)),
      ρ.matrix.rank≤d+1 →
      γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2)-ε <
        statePayoff n (m n) (rankChannel d k n (m n)) ρ := by
  have h := (rank_guarantee_tendsto d k m γ hγ hgain).eventually
    (Ioi_mem_nhds (by linarith : γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2)-ε<
      γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2)))
  filter_upwards [h,eventually_output_gt_input m hγ hgain] with n hn hnm ρ hrank
  exact hn.trans_le (rankChannel_statePayoff_lower d k n (m n) hnm.le ρ hrank)

/-- The liminf statement permits every adversarial sequence of rank-bounded
states. In particular no fixed spectrum or spectral gap is required. -/
theorem rankChannel_liminf_lower (d k : ℕ)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n=>(m n:ℝ)/n) atTop (𝓝 γ))
    (ρ : ℕ→Cloning.MatrixFidelity.State (Fin (d+1+k)))
    (hrank : ∀n,(ρ n).matrix.rank≤d+1) :
    γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2)≤
      liminf (fun n=>statePayoff n (m n) (rankChannel d k n (m n)) (ρ n)) atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := rankChannel_uniform_asymptotic_lower d k m γ hγ hgain ε hε
  have hh : γ ^ (-(((d+1)*(d+1+k)-1:ℕ):ℝ)/2)-ε≤
      liminf (fun n=>statePayoff n (m n) (rankChannel d k n (m n)) (ρ n)) atTop :=
    le_liminf_of_le
      (isCoboundedUnder_ge_of_le atTop (fun n=>
        statePayoff_le_one n (m n) (rankChannel d k n (m n)) (ρ n)))
      (h.mono (fun n hn=>(hn (ρ n) (hrank n)).le))
  linarith

end Cloning.PCTPrescribed
