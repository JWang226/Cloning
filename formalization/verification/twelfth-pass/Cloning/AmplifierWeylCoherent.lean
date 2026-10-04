import Cloning.BosonicAmplifierThermal
import Cloning.WeylDisplacement
import Cloning.InfiniteTraceClassPairing

/-! Exact coherent-vector action of adjoint quantum-limited-amplifier
Kraus operators, retaining the full complex phase. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.BosonicAmplifier
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

lemma sqrt_weight_div_factorial {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n k : ℕ) :
    Real.sqrt (weight q n k) / Real.sqrt ((n + k).factorial : ℝ) =
      Real.sqrt (1 - q) ^ (n + 1) * Real.sqrt q ^ k /
        (Real.sqrt (n.factorial : ℝ) * Real.sqrt (k.factorial : ℝ)) := by
  have hf : ((n + k).choose n : ℝ) * (n.factorial : ℝ) * (k.factorial : ℝ) =
      ((n + k).factorial : ℝ) := by
    exact_mod_cast (show (n + k).choose n * n.factorial * k.factorial = (n + k).factorial by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n k))
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnkf : ((n + k).factorial : ℝ) ≠ 0 := by positivity
  have he : weight q n k / ((n + k).factorial : ℝ) =
      ((1 - q) ^ (n + 1) * q ^ k) / ((n.factorial : ℝ) * (k.factorial : ℝ)) := by
    unfold weight
    apply (div_eq_div_iff hnkf (mul_ne_zero hnf hkf)).mpr
    calc
      _ = (((n + k).choose n : ℝ) * (n.factorial : ℝ) * (k.factorial : ℝ)) *
          ((1 - q) ^ (n + 1) * q ^ k) := by ring
      _ = _ := by rw [hf]; ring
  rw [← Real.sqrt_div (weight_nonneg hq0 hq1 _ _), he,
    Real.sqrt_div (mul_nonneg (pow_nonneg (sub_nonneg.mpr hq1.le) _) (pow_nonneg hq0 _)),
    Real.sqrt_mul (pow_nonneg (sub_nonneg.mpr hq1.le) _),
    Cloning.Thermal.sqrt_nat_pow (sub_nonneg.mpr hq1.le), Cloning.Thermal.sqrt_nat_pow hq0,
    Real.sqrt_mul (Nat.cast_nonneg _)]

/-- The coherent coefficient extracted by the environment-number Kraus label. -/
def coherentKrausAmplitude (q : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (Real.sqrt (1 - q) : ℂ) * ((Real.sqrt q : ℂ) * z) ^ k /
    (Real.sqrt (k.factorial : ℝ) : ℂ) *
      (Real.exp (-q * ‖z‖ ^ 2 / 2) : ℂ)

lemma coherent_kraus_coefficient {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k n : ℕ) (z : ℂ) :
    (Real.sqrt (weight q n k) : ℂ) * Cloning.ComplexCoherent.coherentVector z (n + k) =
      coherentKrausAmplitude q k z *
        Cloning.ComplexCoherent.coherentVector ((Real.sqrt (1 - q) : ℂ) * z) n := by
  rw [Cloning.ComplexCoherent.coherentVector_apply, Cloning.ComplexCoherent.coherentVector_apply]
  have hn : ‖(Real.sqrt (1 - q) : ℂ) * z‖ ^ 2 = (1 - q) * ‖z‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (sub_nonneg.mpr hq1.le)]
  have he : (Real.exp (-q * ‖z‖ ^ 2 / 2) : ℂ) *
      (Real.exp (-((1 - q) * ‖z‖ ^ 2) / 2) : ℂ) =
      (Real.exp (-‖z‖ ^ 2 / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hw := sqrt_weight_div_factorial hq0 hq1 n k
  have hwC : (Real.sqrt (weight q n k) : ℂ) / (Real.sqrt ((n + k).factorial : ℝ) : ℂ) =
      (Real.sqrt (1 - q) : ℂ) ^ (n + 1) * (Real.sqrt q : ℂ) ^ k /
        ((Real.sqrt (n.factorial : ℝ) : ℂ) * (Real.sqrt (k.factorial : ℝ) : ℂ)) := by
    exact_mod_cast hw
  rw [hn]
  unfold coherentKrausAmplitude
  rw [show (Real.sqrt (weight q n k) : ℂ) *
      ((Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * z ^ (n + k) /
        (Real.sqrt ((n + k).factorial : ℝ) : ℂ)) =
      ((Real.sqrt (weight q n k) : ℂ) / (Real.sqrt ((n + k).factorial : ℝ) : ℂ)) *
        ((Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * z ^ (n + k)) by ring, hwC]
  simp only [mul_pow, pow_add, pow_one]
  rw [← he]
  ring

lemma inner_numberBasis (n : ℕ) (v : Fock) : ⟪numberBasis n, v⟫_ℂ = v n := by
  rw [numberBasis_eq_single, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

/-- The adjoint Kraus action on every actual complex coherent vector. -/
theorem kraus_adjoint_coherentVector (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k : ℕ) (z : ℂ) :
    (kraus q hq0 hq1 k).adjoint (Cloning.ComplexCoherent.coherentVector z) =
      coherentKrausAmplitude q k z •
        Cloning.ComplexCoherent.coherentVector ((Real.sqrt (1 - q) : ℂ) * z) := by
  ext n
  rw [← inner_numberBasis, ContinuousLinearMap.adjoint_inner_right, kraus_numberBasis,
    inner_smul_left, inner_numberBasis]
  simp only [Complex.conj_ofReal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact coherent_kraus_coefficient hq0 hq1 k n z

/-- The Kraus amplitudes are one coherent vector, up to the exact common
normalization. This also proves their cross-series summability. -/
lemma coherentKrausAmplitude_eq (q : ℝ) (hq0 : 0 ≤ q) (k : ℕ) (z : ℂ) :
    coherentKrausAmplitude q k z =
      (Real.sqrt (1 - q) : ℂ) *
        Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * z) k := by
  have hn : ‖(Real.sqrt q : ℂ) * z‖ ^ 2 = q * ‖z‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hq0]
  rw [Cloning.ComplexCoherent.coherentVector_apply, hn]
  unfold coherentKrausAmplitude
  have he : -q * ‖z‖ ^ 2 / 2 = -(q * ‖z‖ ^ 2) / 2 := by ring
  rw [he]
  ring

lemma coherentKrausAmplitude_inner_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (v w : ℂ) :
    HasSum (fun k => star (coherentKrausAmplitude q k v) * coherentKrausAmplitude q k w)
      ((1 - q : ℂ) *
        ⟪Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * v),
          Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * w)⟫_ℂ) := by
  have hs := (lp.hasSum_inner
    (Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * v))
    (Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * w))).mul_left (1 - q : ℂ)
  convert hs using 1
  funext k
  simp only [coherentKrausAmplitude_eq q hq0, Complex.star_def, map_mul,
    Complex.conj_ofReal, RCLike.inner_apply]
  have hsq : (Real.sqrt (1 - q) : ℂ) * (Real.sqrt (1 - q) : ℂ) = (1 - q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hq1.le)
  rw [← hsq]
  ring

/-- Exact coherent matrix kernel of the physical amplifier on every complex
trace-class input, including all input coherences. -/
theorem channel_coherent_matrixCoefficient (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (A : TraceClass Fock) (v w : ℂ) :
    ⟪Cloning.ComplexCoherent.coherentVector v,
      ((channel q hq0 hq1).toLinearMap A).1 (Cloning.ComplexCoherent.coherentVector w)⟫_ℂ =
      ((1 - q : ℂ) *
        ⟪Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * v),
          Cloning.ComplexCoherent.coherentVector ((Real.sqrt q : ℂ) * w)⟫_ℂ) *
      ⟪Cloning.ComplexCoherent.coherentVector ((Real.sqrt (1 - q) : ℂ) * v),
        A.1 (Cloning.ComplexCoherent.coherentVector ((Real.sqrt (1 - q) : ℂ) * w))⟫_ℂ := by
  have hs := (channel_hasSum q hq0 hq1 A).mapL
    (traceClassMatrixCoefficient (Cloning.ComplexCoherent.coherentVector v)
      (Cloning.ComplexCoherent.coherentVector w))
  have ht := (coherentKrausAmplitude_inner_hasSum hq0 hq1 v w).mul_right
    ⟪Cloning.ComplexCoherent.coherentVector ((Real.sqrt (1 - q) : ℂ) * v),
      A.1 (Cloning.ComplexCoherent.coherentVector ((Real.sqrt (1 - q) : ℂ) * w))⟫_ℂ
  apply hs.unique
  convert ht using 1
  funext k
  simp only [traceClassMatrixCoefficient_apply, krausTerm, inner_sandwichCLM,
    ContinuousLinearMap.star_eq_adjoint, kraus_adjoint_coherentVector,
    map_smul, inner_smul_left, inner_smul_right, Complex.star_def]
  ring

end Cloning.BosonicAmplifier
