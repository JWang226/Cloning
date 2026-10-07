import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Scalar two-envelope bounds for a support factor times an internal
squared fidelity. The hypotheses here are explicit intermediate data. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PCTProjectorPurity
set_option maxHeartbeats 1000000

def supportLimit (a : ℕ) (δ : ℝ) : ℝ := (1+δ)^(-(a:ℝ))
def internalError (b : ℕ) (δ : ℝ) : ℝ := (1-4*δ^2)^(-((b:ℝ)/2))-1
def lowerEnvelope (a : ℕ) (δ : ℝ) : ℝ := 1-supportLimit a δ
def upperEnvelope (a b : ℕ) (δ : ℝ) : ℝ :=
  1-supportLimit a δ*(1-internalError b δ)

theorem supportLimit_nonneg (a : ℕ) (δ : ℝ) (hδ : 0≤δ) : 0≤supportLimit a δ :=
  Real.rpow_nonneg (by linarith) _

theorem supportLimit_le_one (a : ℕ) (δ : ℝ) (hδ : 0≤δ) : supportLimit a δ≤1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)

/-- Lower and upper asymptotic error envelopes from exact support mass and
an internal squared-error bound. This lemma does not assume a quantum law. -/
theorem eventually_supported_error_envelopes
    (s u : ℕ→ℝ) (S C : ℝ) (hS0 : 0≤S) (hS1 : S≤1)
    (hs : ∀n,0≤s n) (hu : ∀n,0≤u n ∧ u n≤1)
    (hlim : Tendsto s atTop (𝓝 S))
    (hint : ∀η>0,∀ᶠ n in atTop,1-u n^2≤C+η) :
    ∀ε>0,∀ᶠ n in atTop,
      (1-S)-ε≤1-s n*u n^2 ∧
      1-s n*u n^2≤(1-S*(1-C))+ε := by
  intro ε hε
  have habs : Tendsto (fun n=>|s n-S|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hlim.sub_const S).abs
  have hden : 0<2*(|C-1|+1) := by positivity
  have hclose : ∀ᶠ n in atTop,|s n-S|≤ε/(2*(|C-1|+1)) :=
    habs.eventually (eventually_le_nhds (div_pos hε hden))
  have hclose' : ∀ᶠ n in atTop,|s n-S|≤ε :=
    habs.eventually (eventually_le_nhds hε)
  have htwo : ∀ᶠ n in atTop,s n≤2 :=
    hlim.eventually (eventually_le_nhds (by linarith))
  filter_upwards [hclose,hclose',htwo,hint (ε/4) (by positivity)] with n hc hc' hs2 hi
  have hu2 : u n^2≤1 := by nlinarith [(hu n).1,(hu n).2]
  have he0 : 0≤1-u n^2 := by linarith
  have hdiff := (abs_le.mp hc').2
  have hprod := mul_nonneg (hs n) he0
  constructor
  · nlinarith
  · have hI := mul_le_mul_of_nonneg_left hi (hs n)
    have hupper := le_abs_self ((s n-S)*(C-1))
    rw [abs_mul] at hupper
    have heps : |s n-S| *|C-1|≤ε/2 := by
      have hh := (le_div_iff₀ hden).mp hc
      have hp : 0≤|s n-S| := abs_nonneg _
      nlinarith
    have hsmall := mul_le_mul_of_nonneg_right hs2 (show 0≤ε/4 by positivity)
    nlinarith

/-- A rank boundary contributes the same first-order coefficient to both
envelopes; the internal error has zero derivative at zero. -/
theorem lowerEnvelope_hasDerivAt_zero (a : ℕ) :
    HasDerivAt (lowerEnvelope a) (a:ℝ) 0 := by
  have h := (((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const
    (p := -(a:ℝ)) (Or.inl (by norm_num))).const_sub 1
  convert h using 1 <;> simp [lowerEnvelope,supportLimit]

theorem internalError_hasDerivAt_zero (b : ℕ) :
    HasDerivAt (internalError b) 0 0 := by
  have h := (((((hasDerivAt_id (0:ℝ)).pow 2).const_mul 4).const_sub 1).rpow_const
    (p := -((b:ℝ)/2)) (Or.inl (by norm_num))).sub_const 1
  convert h using 1 <;> simp [internalError]

theorem upperEnvelope_hasDerivAt_zero (a b : ℕ) :
    HasDerivAt (upperEnvelope a b) (a:ℝ) 0 := by
  have hs : HasDerivAt (supportLimit a) (-(a:ℝ)) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const
      (p := -(a:ℝ)) (Or.inl (by norm_num))
    convert h using 1 <;> simp [supportLimit]
  have h := (hs.mul ((internalError_hasDerivAt_zero b).const_sub 1)).const_sub 1
  convert h using 1 <;> simp [upperEnvelope,supportLimit,internalError]

theorem lowerEnvelope_div_tendsto (a : ℕ) :
    Tendsto (fun δ=>lowerEnvelope a δ/δ) (𝓝[≠] (0:ℝ)) (𝓝 (a:ℝ)) := by
  have h := (lowerEnvelope_hasDerivAt_zero a).tendsto_slope_zero
  simpa [lowerEnvelope,supportLimit,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

theorem upperEnvelope_div_tendsto (a b : ℕ) :
    Tendsto (fun δ=>upperEnvelope a b δ/δ) (𝓝[≠] (0:ℝ)) (𝓝 (a:ℝ)) := by
  have h := (upperEnvelope_hasDerivAt_zero a b).tendsto_slope_zero
  simpa [upperEnvelope,supportLimit,internalError,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

end Cloning.PCTProjectorPurity
