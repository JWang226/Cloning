import Cloning.WeylDiagonalMultiplier
import Cloning.WeylQuantumPositiveBounds

/-! Complete positivity of the actual trace-class channel implies the diagonal
Weyl cocycle kernel is positive at every finite phase-space configuration. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d : ℕ}

/-- The scalar kernel dictated by the input and output Weyl cocycles. -/
def diagonalQuantumPositiveKernel (f : (Fin d → ℂ) → ℂ) (r : Fin d → ℝ)
    (a b : Fin d → ℂ) : ℂ :=
  displacementPhase (-a) b / displacementPhase (-(diagonalScale r a)) (diagonalScale r b) * f (b - a)

/-- Quantum positive-definiteness at the covariance scaling `r`. This tests
all finite phase-space configurations and all complex scalar coefficients. -/
def IsDiagonalQuantumPositive (f : (Fin d → ℂ) → ℂ) (r : Fin d → ℝ) : Prop :=
  ∀ n : ℕ, ∀ b : Fin n → (Fin d → ℂ), ∀ c : Fin n → ℂ,
    0 ≤ ∑ i, ∑ j, star (c i) * c j * diagonalQuantumPositiveKernel f r (b i) (b j)

/-- A matrix coefficient that removes the output Weyl Gram factor exactly. -/
lemma diagonal_displaced_gram_coefficient (r : Fin d → ℝ) (a b : Fin d → ℂ) (u : Fock d) :
    ⟪displacement (-(diagonalScale r a)) u,
      displacement (diagonalScale r (b - a)) (displacement (-(diagonalScale r b)) u)⟫_ℂ =
    (displacementPhase (-(diagonalScale r a)) (diagonalScale r b))⁻¹ * ⟪u, u⟫_ℂ := by
  have hsum : -(diagonalScale r a) + diagonalScale r b = diagonalScale r (b - a) := by
    rw [diagonalScale_sub]
    abel
  have h := congrArg (fun T : Fock d →L[ℂ] Fock d => T (displacement (-(diagonalScale r b)) u))
    (displacement_comp (-(diagonalScale r a)) (diagonalScale r b))
  simp only [ContinuousLinearMap.comp_apply, displacement_cancel_neg,
    ContinuousLinearMap.smul_apply, hsum] at h
  have h' := congrArg (fun v : Fock d =>
    (displacementPhase (-(diagonalScale r a)) (diagonalScale r b))⁻¹ • v) h
  simp only [smul_smul, inv_mul_cancel₀ (displacementPhase_ne_zero _ _), one_smul] at h'
  rw [← h', inner_smul_right, displacement_inner_map_map]

/-- Every completely positive Weyl multiplier has the quantum-positive
kernel determined by the difference between its two Weyl cocycles. -/
theorem multiplier_isDiagonalQuantumPositive
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d))
    (hCP : Cloning.BoundedOperator.IsCompletelyPositive Ψ)
    (r : Fin d → ℝ) (f : (Fin d → ℂ) → ℂ)
    (hmult : ∀ b, Ψ (displacement b) = f b • displacement (diagonalScale r b)) :
    IsDiagonalQuantumPositive f r := by
  intro n b c
  have hgram := Cloning.BoundedOperator.gram_blockPositive (fun i : Fin n => displacement (b i))
  have h := hCP n _ hgram (fun i => c i •
    displacement (-(diagonalScale r (b i))) (coherentVector (0 : Fin d → ℂ)))
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [displacement_adjoint, displacement_comp]
  simp only [map_smul, hmult, ContinuousLinearMap.smul_apply, inner_smul_left,
    inner_smul_right]
  rw [show -b i + b j = b j - b i by abel, diagonal_displaced_gram_coefficient]
  simp only [inner_self_eq_norm_sq_to_K, coherentVector_norm,
    RCLike.ofReal_eq_complex_ofReal, one_pow,
    Complex.ofReal_one, mul_one, diagonalQuantumPositiveKernel, starRingEnd_apply, div_eq_mul_inv]
  ring


variable {f : (Fin d → ℂ) → ℂ} {r : Fin d → ℝ}

lemma IsDiagonalQuantumPositive.two_point (hf : IsDiagonalQuantumPositive f r)
    (hf0 : f 0 = 1) (b : Fin d → ℂ) (u v : ℂ) :
    0 ≤ star u * u + star u * v * f b + star v * u * f (-b) + star v * v := by
  have h := hf 2 ![0, b] ![u, v]
  simpa [Fin.sum_univ_two, diagonalQuantumPositiveKernel, hf0, add_assoc] using h

/-- Conjugate symmetry follows from actual complete positivity. -/
theorem IsDiagonalQuantumPositive.conj_symm (hf : IsDiagonalQuantumPositive f r)
    (hf0 : f 0 = 1) (b : Fin d → ℂ) : f (-b) = star (f b) := by
  have h1 := (Complex.nonneg_iff.mp (hf.two_point hf0 b 1 1)).2
  have hI := (Complex.nonneg_iff.mp (hf.two_point hf0 b 1 Complex.I)).2
  simp only [map_one, one_mul, mul_one, Complex.add_im, Complex.one_im,
    Complex.star_def, Complex.conj_I, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 hI
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

/-- The diagonal gain case has the same unit modulus bound. -/
theorem IsDiagonalQuantumPositive.norm_le_one (hf : IsDiagonalQuantumPositive f r)
    (hf0 : f 0 = 1) (b : Fin d → ℂ) : ‖f b‖ ≤ 1 := by
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

/-- All regular quantum-positive multiplier data are derived from the actual
channel, including positivity at every finite ancilla. -/
theorem quantumChannel_regular_diagonalQuantumPositive_multiplier
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : Fin d → ℝ)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale r a) (Φ.toLinearMap T)) :
    (∀ b, Φ.heisenberg (displacement b) =
      diagonalWeylMultiplier Φ.heisenberg r b • displacement (diagonalScale r b)) ∧
    diagonalWeylMultiplier Φ.heisenberg r 0 = 1 ∧
    Continuous (diagonalWeylMultiplier Φ.heisenberg r) ∧
    IsDiagonalQuantumPositive (diagonalWeylMultiplier Φ.heisenberg r) r ∧
    (∀ b, ‖diagonalWeylMultiplier Φ.heisenberg r b‖ ≤ 1) := by
  obtain ⟨hmult, hzero, hcont⟩ := quantumChannel_diagonal_weyl_multiplier Φ r hΦ
  have hpos : IsDiagonalQuantumPositive (diagonalWeylMultiplier Φ.heisenberg r) r :=
    multiplier_isDiagonalQuantumPositive Φ.heisenberg
      (heisenbergDual_completelyPositive
        Φ.toPositiveTracePreservingMap.toContinuousLinearMap Φ.completelyPositive) r _ hmult
  exact ⟨hmult, hzero, hcont, hpos, fun b => hpos.norm_le_one hzero b⟩

end Cloning.MultimodeCoherent
