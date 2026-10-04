import Cloning.WeylQuantumPositiveDual
import Cloning.HeisenbergDualContinuity

/-! Normalization and quantum positivity give conjugate symmetry and the
unit modulus bound. These bounds are derived from complete positivity of
the actual trace-class channel, not an assumed contraction of its dual. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ} {f : (Fin d → ℂ) → ℂ} {r : ℝ}

lemma IsQuantumPositive.two_point (hf : IsQuantumPositive f r) (hf0 : f 0 = 1)
    (b : Fin d → ℂ) (u v : ℂ) :
    0 ≤ star u * u + star u * v * f b + star v * u * f (-b) + star v * v := by
  have h := hf 2 ![0, b] ![u, v]
  simpa [Fin.sum_univ_two, quantumPositiveKernel, hf0, add_assoc] using h

/-- The negative-frequency value is forced by quantum positivity. -/
theorem IsQuantumPositive.conj_symm (hf : IsQuantumPositive f r) (hf0 : f 0 = 1)
    (b : Fin d → ℂ) : f (-b) = star (f b) := by
  have h1 := (Complex.nonneg_iff.mp (hf.two_point hf0 b 1 1)).2
  have hI := (Complex.nonneg_iff.mp (hf.two_point hf0 b 1 Complex.I)).2
  simp only [map_one, one_mul, mul_one, Complex.add_im, Complex.one_im,
    Complex.star_def, Complex.conj_I, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 hI
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

/-- Every normalized quantum-positive multiplier has modulus at most one. -/
theorem IsQuantumPositive.norm_le_one (hf : IsQuantumPositive f r) (hf0 : f 0 = 1)
    (b : Fin d → ℂ) : ‖f b‖ ≤ 1 := by
  have h := (Complex.nonneg_iff.mp (hf.two_point hf0 b 1 (-star (f b)))).1
  rw [hf.conj_symm hf0 b] at h
  have heq : star (1 : ℂ) * 1 + star (1 : ℂ) * (-star (f b)) * f b +
      star (-star (f b)) * 1 * star (f b) + star (-star (f b)) * (-star (f b)) =
      1 - star (f b) * f b := by simp; ring
  rw [heq] at h
  change 0 ≤ (1 - (starRingEnd ℂ) (f b) * f b).re at h
  rw [← Complex.normSq_eq_conj_mul_self] at h
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (f b)]

/-- Every physical covariant CPTP channel has a normalized, continuous,
quantum-positive Weyl multiplier of modulus at most one. -/
theorem quantumChannel_regular_quantumPositive_multiplier
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ.toLinearMap T)) :
    (∀ b, Φ.heisenberg (displacement b) =
      weylMultiplier Φ.heisenberg r b • displacement (r • b)) ∧
    weylMultiplier Φ.heisenberg r 0 = 1 ∧
    Continuous (weylMultiplier Φ.heisenberg r) ∧
    IsQuantumPositive (weylMultiplier Φ.heisenberg r) r ∧
    (∀ b, ‖weylMultiplier Φ.heisenberg r b‖ ≤ 1) := by
  obtain ⟨hmult, hzero⟩ := quantumChannel_weyl_multiplier Φ r hΦ
  have hpos : IsQuantumPositive (weylMultiplier Φ.heisenberg r) r :=
    traceClass_covariant_multiplier_isQuantumPositive
      Φ.toPositiveTracePreservingMap.toContinuousLinearMap Φ.completelyPositive r
      (heisenbergDual_weyl_covariance _ r hΦ)
  exact ⟨hmult, hzero, continuous_traceClass_weylMultiplier _ r hΦ,
    hpos, fun b => hpos.norm_le_one hzero b⟩

end Cloning.MultimodeCoherent
