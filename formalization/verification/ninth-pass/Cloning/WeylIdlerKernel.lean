import Cloning.WeylQuantumPositiveBounds

/-! The amplifier multiplier's twisted positivity becomes ordinary Weyl
characteristic positivity after the required phase conjugation and noise
rescaling. This identifies the exact CCR form entering idler reconstruction.
Existence of a density operator representing this function is not assumed
or claimed here. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d : ℕ}

/-- The standard finite Weyl-Gram positivity condition for an idler state. -/
def IsWeylCharacteristicPositive (g : (Fin d → ℂ) → ℂ) : Prop :=
  ∀ n : ℕ, ∀ b : Fin n → (Fin d → ℂ), ∀ c : Fin n → ℂ,
    0 ≤ ∑ i, ∑ j, star (c i) * c j *
      (displacementPhase (-(b i)) (b j) * g (b j - b i))

/-- The residual amplifier symplectic form is the ordinary idler symplectic
form after complex conjugation and multiplication by `sqrt(r²-1)`. -/
theorem amplifier_phase_ratio (r s : ℝ) (hs : s ^ 2 = r ^ 2 - 1)
    (a b : Fin d → ℂ) :
    displacementPhase (-a) b / displacementPhase (-(r • a)) (r • b) =
      displacementPhase (-(s • star a)) (s • star b) := by
  have hsC : (s : ℂ) ^ 2 = (r : ℂ) ^ 2 - 1 := by exact_mod_cast hs
  simp only [displacementPhase, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.star_apply, Complex.real_smul,
    Complex.star_def, ComplexCoherent.displacementPhase, ← Complex.exp_sub,
    map_neg, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  congr 1
  linear_combination -((a i * (starRingEnd ℂ) (b i) -
    (starRingEnd ℂ) (a i) * b i) / 2) * hsC

lemma idler_frequency_inverse (s : ℝ) (hs : s ≠ 0) (a : Fin d → ℂ) :
    s • star ((s⁻¹) • star a) = a := by
  simp only [star_smul, star_inv, star_trivial, star_star, smul_smul,
    mul_inv_cancel₀ hs, one_smul]

/-- The rescaled, phase-conjugated multiplier meets the standard quantum
Bochner positivity tests for an actual bosonic idler. -/
theorem IsQuantumPositive.idler_characteristic_positive
    {f : (Fin d → ℂ) → ℂ} {r s : ℝ}
    (hf : IsQuantumPositive f r) (hs : s ≠ 0) (hsq : s ^ 2 = r ^ 2 - 1) :
    IsWeylCharacteristicPositive (fun a => f ((s⁻¹) • star a)) := by
  intro n b c
  have h := hf n (fun i => (s⁻¹) • star (b i)) c
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [quantumPositiveKernel, amplifier_phase_ratio r s hsq,
    idler_frequency_inverse s hs, idler_frequency_inverse s hs]
  simp only [star_sub, smul_sub]

/-- The idler characteristic candidate in the amplifying regime. -/
def amplifierIdlerFunction (f : (Fin d → ℂ) → ℂ) (r : ℝ) (a : Fin d → ℂ) : ℂ :=
  f ((Real.sqrt (r ^ 2 - 1))⁻¹ • star a)

/-- An actual covariant CPTP amplifier supplies all the normalized, regular
quantum-Bochner data for the joint idler in any finite number of modes.
The separate density-operator existence theorem is the remaining step. -/
theorem quantumChannel_idler_characteristic_data
    (Φ : Cloning.InfiniteTraceClass.QuantumChannel (Fock d) (Fock d))
    (r : ℝ) (hr : 1 < r)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ.toLinearMap T)) :
    let f := weylMultiplier Φ.heisenberg r
    let g := amplifierIdlerFunction f r
    g 0 = 1 ∧ Continuous g ∧ IsWeylCharacteristicPositive g ∧
      (∀ a, ‖g a‖ ≤ 1) ∧
      (∀ a, f a = g (Real.sqrt (r ^ 2 - 1) • star a)) := by
  dsimp only
  obtain ⟨_, hf0, hfcont, hfpos, hfnorm⟩ :=
    quantumChannel_regular_quantumPositive_multiplier Φ r hΦ
  have hsq : 0 < r ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (r ^ 2 - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsq)
  refine ⟨?_, ?_, hfpos.idler_characteristic_positive hs (Real.sq_sqrt hsq.le), ?_, ?_⟩
  · simpa only [amplifierIdlerFunction, star_zero, smul_zero] using hf0
  · exact hfcont.comp (continuous_const.smul continuous_star)
  · intro a
    exact hfnorm _
  · intro a
    unfold amplifierIdlerFunction
    congr 1
    simp only [star_smul, star_trivial, star_star, smul_smul, inv_mul_cancel₀ hs, one_smul]

end Cloning.MultimodeCoherent
