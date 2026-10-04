import Cloning.PCTProjectorPurityEnvelope
import Cloning.ScalarTaylorRemainder

/-! Explicit next-order envelope errors and target-error bracketing. These
are scalar consequences of the physical two-envelope theorem; no convergence
of the physical fidelity at fixed gain is assumed. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.PCTProjectorPurity

private theorem linear_remainder {f : ℝ→ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (fun x=>f x-(f 0+deriv f 0*x)) =O[𝓝 (0:ℝ)] (fun x=>x^2) := by
  have h := ScalarTaylor.local_taylor_isBigO 1 hf
  convert h using 1
  · ext x
    simp only [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
      iteratedDeriv_one,smul_eq_mul,sub_zero]
    norm_num
    ring
  · simp

/-- The internal purity correction has the fourth-order remainder stated in
the manuscript, including its exact quadratic coefficient. -/
theorem internalError_quartic_remainder (b : ℕ) :
    (fun δ=>internalError b δ-2*(b:ℝ)*δ^2) =O[𝓝 (0:ℝ)] (fun δ=>δ^4) := by
  let f : ℝ→ℝ := fun x=>(1-4*x)^(-((b:ℝ)/2))-1
  have hf : ContDiffAt ℝ 2 f 0 :=
    ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).rpow_const_of_ne
      (by norm_num)).sub contDiffAt_const
  have hd : HasDerivAt f (2*(b:ℝ)) 0 := by
    have h := (((hasDerivAt_id (0:ℝ)).const_mul 4).const_sub 1).rpow_const
      (p := -((b:ℝ)/2)) (Or.inl (by norm_num))
    convert h.sub_const 1 using 1 <;> simp [f] <;> ring
  have h := (linear_remainder hf).comp_tendsto
    (show Tendsto (fun δ:ℝ=>δ^2) (𝓝 0) (𝓝 0) by
      simpa using (tendsto_id : Tendsto (fun δ:ℝ=>δ) (𝓝 0) (𝓝 0)).pow 2)
  simpa [f,internalError,hd.deriv,Function.comp_def,← pow_mul] using h

theorem lowerEnvelope_quadratic_remainder (a : ℕ) :
    (fun δ=>lowerEnvelope a δ-(a:ℝ)*δ) =O[𝓝 (0:ℝ)] (fun δ=>δ^2) := by
  have hf : ContDiffAt ℝ 2 (lowerEnvelope a) 0 :=
    contDiffAt_const.sub ((contDiffAt_const.add contDiffAt_id).rpow_const_of_ne
      (by norm_num))
  simpa [lowerEnvelope,supportLimit,(lowerEnvelope_hasDerivAt_zero a).deriv] using
    linear_remainder hf

theorem upperEnvelope_quadratic_remainder (a b : ℕ) :
    (fun δ=>upperEnvelope a b δ-(a:ℝ)*δ) =O[𝓝 (0:ℝ)] (fun δ=>δ^2) := by
  have hs : ContDiffAt ℝ 2 (supportLimit a) 0 :=
    (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by norm_num)
  have hi : ContDiffAt ℝ 2 (internalError b) 0 :=
    ((contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.pow 2))).rpow_const_of_ne
      (by norm_num)).sub contDiffAt_const
  have hf : ContDiffAt ℝ 2 (upperEnvelope a b) 0 :=
    contDiffAt_const.sub (hs.mul (contDiffAt_const.sub hi))
  simpa [upperEnvelope,supportLimit,internalError,(upperEnvelope_hasDerivAt_zero a b).deriv]
    using linear_remainder hf

private theorem scaled_ratio_tendsto {f : ℝ→ℝ} {a : ℝ}
    (hf0 : f 0=0) (hf : HasDerivAt f a 0) (c : ℝ) :
    Tendsto (fun ε=>f (c*ε)/ε) (𝓝[≠] (0:ℝ)) (𝓝 (a*c)) := by
  have hc : HasDerivAt (fun ε=>f (c*ε)) (a*c) 0 := by
    have hf' : HasDerivAt f a (c * id (0:ℝ)) := by simpa using hf
    simpa using hf'.comp 0 ((hasDerivAt_id (0:ℝ)).const_mul c)
  simpa [hf0,smul_eq_mul,div_eq_mul_inv,mul_comm] using hc.tendsto_slope_zero

/-- For a positive rank-boundary coefficient, the two envelopes bracket a
small target error at gains (1±η)ε/a. This is an iterated-limit certificate. -/
theorem envelopes_target_bracket (a b : ℕ) (ha : 0<a) {η : ℝ}
    (hη : 0<η) (hη1 : η<1) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      upperEnvelope a b ((1-η)*ε/a)<ε ∧
      ε<lowerEnvelope a ((1+η)*ε/a) := by
  have ha0 : (a:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt ha
  have hl := scaled_ratio_tendsto
    (show lowerEnvelope a 0=0 by simp [lowerEnvelope,supportLimit])
    (lowerEnvelope_hasDerivAt_zero a) ((1+η)/a)
  have hu := scaled_ratio_tendsto
    (show upperEnvelope a b 0=0 by simp [upperEnvelope,supportLimit,internalError])
    (upperEnvelope_hasDerivAt_zero a b) ((1-η)/a)
  have hal : (a:ℝ)*((1+η)/a)=1+η := by field_simp
  have hau : (a:ℝ)*((1-η)/a)=1-η := by field_simp
  rw [hal] at hl
  rw [hau] at hu
  have hmono : 𝓝[>] (0:ℝ)≤𝓝[≠] (0:ℝ) :=
    nhdsWithin_mono _ (by intro x hx; simpa using ne_of_gt hx)
  have hl' := (hl.mono_left hmono).eventually (Ioi_mem_nhds (show 1<1+η by linarith))
  have hu' := (hu.mono_left hmono).eventually (Iio_mem_nhds (show 1-η<1 by linarith))
  filter_upwards [hl',hu',self_mem_nhdsWithin] with ε hlε huε hε
  have hε0 : 0<ε := hε
  constructor
  · have h := (div_lt_one hε0).mp huε
    simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
  · have h := (one_lt_div hε0).mp hlε
    simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h

end Cloning.PCTProjectorPurity
