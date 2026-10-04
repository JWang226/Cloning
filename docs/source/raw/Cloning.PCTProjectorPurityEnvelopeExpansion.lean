import Cloning.PCTProjectorPurityEnvelope
import Cloning.ScalarTaylorRemainder

/-! Quadratic internal error and the precise two-stage small-gain coefficient. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.PCTProjectorPurity
set_option maxHeartbeats 1000000

theorem internalError_isBigO_square (b : ℕ) :
    internalError b =O[𝓝 (0:ℝ)] (fun δ=>δ^2) := by
  have hf : ContDiffAt ℝ 2 (internalError b) 0 := by
    unfold internalError
    exact (((contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.pow 2))).rpow_const_of_ne
      (by norm_num)).sub contDiffAt_const)
  have h := Cloning.ScalarTaylor.local_taylor_isBigO 1 hf
  have hz : internalError b 0=0 := by simp [internalError]
  have hd : deriv (internalError b) 0=0 := (internalError_hasDerivAt_zero b).deriv
  simpa only [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
    Nat.zero_add,iteratedDeriv_one,smul_eq_mul,hz,hd,mul_zero,zero_mul,add_zero,sub_zero] using h

/-- If the physical errors lie between these envelopes after taking large
sample sizes, their normalized small-gain coefficient is exactly a. The
statement allows all parameters in the index type to vary uniformly. -/
theorem error_envelopes_first_order {ι : Type*} (a b : ℕ) (δ₀ : ℝ) (hδ₀ : 0<δ₀)
    (E : ℝ→ℕ→ι→ℝ)
    (henv : ∀δ,0<δ→δ<δ₀→∀ε>0,∀ᶠ n in atTop,∀i,
      lowerEnvelope a δ-ε≤E δ n i ∧ E δ n i≤upperEnvelope a b δ+ε) :
    ∀η>0,∀ᶠ δ in 𝓝[>] (0:ℝ),∀ᶠ n in atTop,∀i,
      |E δ n i/δ-(a:ℝ)|≤η := by
  intro η hη
  have hfilter : (𝓝[>] (0:ℝ))≤𝓝[≠] (0:ℝ) :=
    nhdsWithin_mono 0 (fun δ hδ=>ne_of_gt hδ)
  have hl := (lowerEnvelope_div_tendsto a).mono_left hfilter
  have hu := (upperEnvelope_div_tendsto a b).mono_left hfilter
  have hlo : ∀ᶠ δ in 𝓝[>] (0:ℝ),(a:ℝ)-η/2≤lowerEnvelope a δ/δ :=
    hl.eventually (eventually_ge_nhds (by linarith))
  have hup : ∀ᶠ δ in 𝓝[>] (0:ℝ),upperEnvelope a b δ/δ≤(a:ℝ)+η/2 :=
    hu.eventually (eventually_le_nhds (by linarith))
  have hsmall : ∀ᶠ δ in 𝓝[>] (0:ℝ),δ<δ₀ :=
    (eventually_lt_nhds hδ₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall,hlo,hup] with δ hδ hs hl hu
  have hd : 0<δ := hδ
  filter_upwards [henv δ hd hs (δ*(η/2)) (by positivity)] with n hn i
  have ha := div_le_div_of_nonneg_right (hn i).1 hd.le
  have hb := div_le_div_of_nonneg_right (hn i).2 hd.le
  have he : (δ*(η/2))/δ=η/2 := mul_div_cancel_left₀ _ hd.ne'
  simp only [sub_div,add_div,he] at ha hb
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end Cloning.PCTProjectorPurity
