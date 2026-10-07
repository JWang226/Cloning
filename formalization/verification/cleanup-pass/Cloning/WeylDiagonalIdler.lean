import Cloning.WeylDiagonalQuantumPositive
import Cloning.WeylIdlerKernel

/-! Independent amplifying mode gains produce one joint idler characteristic
function. The residual CCR form is transformed to the standard Weyl form by
coordinatewise noise scaling and phase conjugation. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d : ℕ}

/-- The diagonal residual cocycle is the standard idler cocycle after phase
conjugation, with the exact independent noise amplitudes. -/
theorem diagonal_amplifier_phase_ratio (r s : Fin d → ℝ)
    (hs : ∀ i, s i ^ 2 = r i ^ 2 - 1) (a b : Fin d → ℂ) :
    displacementPhase (-a) b /
        displacementPhase (-(diagonalScale r a)) (diagonalScale r b) =
      displacementPhase (-(diagonalScale s (star a))) (diagonalScale s (star b)) := by
  simp only [displacementPhase, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hsC : (s i : ℂ) ^ 2 = (r i : ℂ) ^ 2 - 1 := by exact_mod_cast hs i
  simp only [Pi.neg_apply, diagonalScale, Pi.star_apply, Complex.star_def,
    ComplexCoherent.displacementPhase, ← Complex.exp_sub, map_neg, map_mul,
    Complex.conj_ofReal, starRingEnd_self_apply]
  congr 1
  linear_combination -((a i * (starRingEnd ℂ) (b i) -
    (starRingEnd ℂ) (a i) * b i) / 2) * hsC

lemma diagonal_idler_frequency_inverse (s : Fin d → ℝ) (hs : ∀ i, s i ≠ 0)
    (a : Fin d → ℂ) :
    diagonalScale s (star (diagonalScale (fun i => (s i)⁻¹) (star a))) = a := by
  ext i
  simp [diagonalScale, hs]

lemma diagonal_idler_frequency_inverse' (s : Fin d → ℝ) (hs : ∀ i, s i ≠ 0)
    (a : Fin d → ℂ) :
    diagonalScale (fun i => (s i)⁻¹) (star (diagonalScale s (star a))) = a := by
  ext i
  simp [diagonalScale, hs]

/-- The channel-derived diagonal kernel meets the standard finite Weyl tests. -/
theorem IsDiagonalQuantumPositive.idler_characteristic_positive
    {f : (Fin d → ℂ) → ℂ} {r s : Fin d → ℝ}
    (hf : IsDiagonalQuantumPositive f r) (hs : ∀ i, s i ≠ 0)
    (hsq : ∀ i, s i ^ 2 = r i ^ 2 - 1) :
    IsWeylCharacteristicPositive
      (fun a => f (diagonalScale (fun i => (s i)⁻¹) (star a))) := by
  intro n b c
  have h := hf n (fun i => diagonalScale (fun j => (s j)⁻¹) (star (b i))) c
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [diagonalQuantumPositiveKernel, diagonal_amplifier_phase_ratio r s hsq,
    diagonal_idler_frequency_inverse s hs, diagonal_idler_frequency_inverse s hs]
  simp only [star_sub, diagonalScale_sub]

/-- Amplitude gain associated with each positive power gain. -/
def diagonalGainAmplitude (G : Fin d → ℝ) : Fin d → ℝ := fun i => Real.sqrt (G i)

/-- Added-noise amplitude in each amplifying mode. -/
def diagonalNoiseAmplitude (G : Fin d → ℝ) : Fin d → ℝ := fun i => Real.sqrt (G i - 1)

/-- The characteristic candidate for the joint, potentially correlated idler. -/
def diagonalAmplifierIdlerFunction (f : (Fin d → ℂ) → ℂ) (G : Fin d → ℝ)
    (a : Fin d → ℂ) : ℂ :=
  f (diagonalScale (fun i => (diagonalNoiseAmplitude G i)⁻¹) (star a))

/-- Every actual CPTP channel covariant with independent gains `G i > 1`
supplies normalized continuous quantum-Bochner data for a joint idler. The
Weyl multiplier identity and the phase-conjugated reconstruction are included. -/
theorem quantumChannel_diagonal_idler_characteristic_data
    (Φ : QuantumChannel (Fock d) (Fock d))
    (G : Fin d → ℝ) (hG : ∀ i, 1 < G i)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a) (Φ.toLinearMap T)) :
    let f := diagonalWeylMultiplier Φ.heisenberg (diagonalGainAmplitude G)
    let g := diagonalAmplifierIdlerFunction f G
    (∀ a, Φ.heisenberg (displacement a) =
      f a • displacement (diagonalScale (diagonalGainAmplitude G) a)) ∧
    g 0 = 1 ∧ Continuous g ∧ IsWeylCharacteristicPositive g ∧
      (∀ a, ‖g a‖ ≤ 1) ∧
      (∀ a, f a = g (diagonalScale (diagonalNoiseAmplitude G) (star a))) := by
  dsimp only
  obtain ⟨hmult, hf0, hfcont, hfpos, hfnorm⟩ :=
    quantumChannel_regular_diagonalQuantumPositive_multiplier Φ (diagonalGainAmplitude G) hΦ
  have hs (i) : diagonalNoiseAmplitude G i ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (hG i)))
  have hsq (i) : diagonalNoiseAmplitude G i ^ 2 = diagonalGainAmplitude G i ^ 2 - 1 := by
    rw [diagonalNoiseAmplitude, diagonalGainAmplitude,
      Real.sq_sqrt (sub_nonneg.mpr (hG i).le), Real.sq_sqrt (by linarith [hG i])]
  refine ⟨hmult, ?_, ?_, hfpos.idler_characteristic_positive hs hsq, ?_, ?_⟩
  · simpa only [diagonalAmplifierIdlerFunction, star_zero, diagonalScale_zero] using hf0
  · exact hfcont.comp ((continuous_diagonalScale _).comp continuous_star)
  · intro a
    exact hfnorm _
  · intro a
    unfold diagonalAmplifierIdlerFunction
    rw [diagonal_idler_frequency_inverse' _ hs]

end Cloning.MultimodeCoherent
