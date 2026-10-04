import Cloning.PhysicalAllStateMinimax
import Cloning.PCTWernerLower

/-! The physical full-environment PCT channel gives a spectrum-independent
finite lower bound and the stated all-density minimax liminf. -/
noncomputable section
open scoped BigOperators Topology Classical Matrix
open Filter
namespace Cloning.PhysicalAllStateMinimax
open Cloning.PCT Cloning.PCTPhysicalState Cloning.TensorCloning Cloning.InfiniteTraceClass
open Cloning.PCTRankAdapted Cloning.PCTPrescribed
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000

attribute [local instance] stateNonempty

/-- The candidate is the same fixed physical channel for every density,
including singular and repeated-eigenvalue inputs. -/
theorem fullChannel_payoff_lower (d n m : ℕ) (hnm : n<m)
    (ρ : Cloning.MatrixFidelity.State (Fin (d+1))) :
    Real.sqrt (wernerScale n m (d*(d+2)))≤statePayoff n m (fullChannel d n m) ρ := by
  rw [fullChannel,extendChannel_payoff_of_gt _ n m hnm ρ]
  have hh : Real.sqrt (wernerScale n (n+(m-n)) (d*(d+2)))≤
      statePayoff n (n+(m-n)) (PCTGlobal.channel (purification_register_card d) n (m-n)) ρ :=
    outputState_fidelity_lower (purification_register_card d) ρ n (m-n)
  convert hh using 1
  rw [Nat.add_sub_of_le hnm.le]

theorem sqrt_wernerScale_le_value (d n m : ℕ) (hnm : n<m) :
    Real.sqrt (wernerScale n m (d*(d+2)))≤value d n m := by
  exact LAN.candidate_le_minimaxValue _ (fullChannel d n m) _
    (statePayoff_le_one n m) (fullChannel_payoff_lower d n m hnm) (statePayoff_nonneg n m)

lemma sqrt_wernerScale_tendsto (s : ℕ) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n => Real.sqrt (wernerScale n (m n) s)) atTop (𝓝 (γ^(-(s:ℝ)/2))) := by
  have hh := sqrt_supportFactor_tendsto m hγ hgain 0 s
  have he (n : ℕ) : supportFactor n (m n) 0 s=wernerScale n (m n) s := by
    simp [supportFactor,wernerScale]
  simpa only [he,Nat.cast_zero,sub_zero] using hh

/-- Every fixed gain admits the uniform PCT lower envelope. -/
theorem eventually_value_lower (d : ℕ) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,γ^(-(((d+1:ℕ):ℝ)^2-1)/2)-ε<value d n (m n) := by
  have hh := sqrt_wernerScale_tendsto (d*(d+2)) m γ hγ hgain
  have he : -((d*(d+2):ℕ):ℝ)/2= -(((d+1:ℕ):ℝ)^2-1)/2 := by push_cast; ring
  rw [he] at hh
  filter_upwards [hh.eventually (eventually_gt_nhds (sub_lt_self _ hε)),
    eventually_output_gt_input m hγ hgain] with n hn hnm
  exact hn.trans_le (sqrt_wernerScale_le_value d n (m n) hnm)

/-- The manuscript all-density minimax lower bound, with no spectral or
rank premise on the adversarial density matrices. -/
theorem lower_le_liminf_value (d : ℕ) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    γ^(-(((d+1:ℕ):ℝ)^2-1)/2)≤liminf (fun n => value d n (m n)) atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (fun n => value_le_one d n (m n)))
    (Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => value_nonneg d n (m n))))).mpr
  intro a ha
  have hh := eventually_value_lower d m γ hγ hgain
    (γ^(-(((d+1:ℕ):ℝ)^2-1)/2)-a) (sub_pos.mpr ha)
  simpa only [sub_sub_cancel] using hh

end Cloning.PhysicalAllStateMinimax
