import Cloning.PCTProjectorPurityEnvelopeLimits

/-! Concrete sample-gain brackets for the actual projector PCT channel,
uniformly in the unknown projector and with the order of limits explicit. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PCTProjectorPurity
open Cloning.PhysicalFlatGrassmann

/-- At gains (1±η)ε/a, the actual squared fidelity is respectively above
and below 1−ε for all sufficiently large samples. The sample cutoff may
depend on ε, exactly as required by the iterated limit. -/
theorem physical_target_brackets (d k : ℕ) (hk : 0<k) (t : ℝ→ℕ→ℕ)
    (hgain : ∀δ,0<δ→δ<1/(2*((d+1:ℕ):ℝ))→
      Tendsto (fun n=>((n+t δ n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ)))
    {η : ℝ} (hη : 0<η) (hη1 : η<1) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ᶠ (n : ℕ) in atTop,∀P : Projector (d+1) k,
      1-ε<PhysicalFlatPCT.fidelity d k P n (t ((1-η)*ε/(((d+1)*k:ℕ):ℝ)) n)^2 ∧
      PhysicalFlatPCT.fidelity d k P n (t ((1+η)*ε/(((d+1)*k:ℕ):ℝ)) n)^2<1-ε := by
  let a := (d+1)*k
  have haN : 0<a := Nat.mul_pos (by omega) hk
  have ha : (0:ℝ)<a := by exact_mod_cast haN
  have hid : Tendsto (fun ε:ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hl : Tendsto (fun ε=>(1-η)*ε/(a:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (hid.const_mul (1-η)).div_const (a:ℝ)
  have hu : Tendsto (fun ε=>(1+η)*ε/(a:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (hid.const_mul (1+η)).div_const (a:ℝ)
  have hb : (0:ℝ)<1/(2*((d+1:ℕ):ℝ)) := by positivity
  filter_upwards [envelopes_target_bracket a (d*(d+2)) haN hη hη1,
    hl.eventually_lt_const hb,hu.eventually_lt_const hb,self_mem_nhdsWithin]
    with ε he hls hus hε
  have hε0 : 0<ε := hε
  have hlp : 0<(1-η)*ε/(a:ℝ) := div_pos (mul_pos (by linarith) hε0) ha
  have hup : 0<(1+η)*ε/(a:ℝ) := div_pos (mul_pos (by linarith) hε0) ha
  have hL := physical_error_envelopes d k (t ((1-η)*ε/a)) ((1-η)*ε/a)
    hlp hls (hgain _ hlp hls)
    ((ε-upperEnvelope a (d*(d+2)) ((1-η)*ε/a))/2) (by linarith [he.1])
  have hU := physical_error_envelopes d k (t ((1+η)*ε/a)) ((1+η)*ε/a)
    hup hus (hgain _ hup hus)
    ((lowerEnvelope a ((1+η)*ε/a)-ε)/2) (by linarith [he.2])
  filter_upwards [hL,hU] with n hLn hUn P
  have hleft := (hLn P).2
  have hright := (hUn P).1
  change 1-ε<PhysicalFlatPCT.fidelity d k P n (t ((1-η)*ε/a) n)^2 ∧
    PhysicalFlatPCT.fidelity d k P n (t ((1+η)*ε/a) n)^2<1-ε
  change 1-PhysicalFlatPCT.fidelity d k P n (t ((1-η)*ε/a) n)^2≤
    upperEnvelope a (d*(d+2)) ((1-η)*ε/a)+
      (ε-upperEnvelope a (d*(d+2)) ((1-η)*ε/a))/2 at hleft
  change lowerEnvelope a ((1+η)*ε/a)-(lowerEnvelope a ((1+η)*ε/a)-ε)/2≤
    1-PhysicalFlatPCT.fidelity d k P n (t ((1+η)*ε/a) n)^2 at hright
  constructor <;> linarith [he.1,he.2]

end Cloning.PCTProjectorPurity
