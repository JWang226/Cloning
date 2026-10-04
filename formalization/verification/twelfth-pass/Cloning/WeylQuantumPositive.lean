import Cloning.WeylCovariantMultiplier
import Cloning.WeylMultimodeChannel

/-! Complete positivity forces the exact quantum positive-definiteness
condition on the Weyl multiplier. The proof uses positive Weyl Gram blocks
and tests their completely positive images on displaced copies of the vacuum.
The displacement phase is the actual phase of the constructed Fock operators.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators

namespace Cloning.BoundedOperator

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι]

/-- Positivity on the finite Hilbert direct sum for bounded operator blocks. -/
def BlockPositive (A : ι → ι → H →L[ℂ] H) : Prop :=
  ∀ x : ι → H, 0 ≤ ∑ i, ∑ j, ⟪x i, A i j (x j)⟫_ℂ

/-- Complete positivity of a bounded-operator map, at every finite ancilla. -/
def IsCompletelyPositive (Ψ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ n : ℕ, ∀ A : Fin n → Fin n → H →L[ℂ] H,
    BlockPositive A → BlockPositive (fun i j => Ψ (A i j))

/-- Operator Gram matrices are positive at arbitrary finite size. -/
theorem gram_blockPositive (V : ι → H →L[ℂ] K) :
    BlockPositive (fun i j => (V i).adjoint.comp (V j)) := by
  intro x
  have h : (0 : ℂ) ≤ ⟪∑ i, V i (x i), ∑ j, V j (x j)⟫_ℂ := by
    apply RCLike.nonneg_iff.mpr
    exact ⟨inner_self_nonneg, inner_self_im _⟩
  rw [sum_inner] at h
  simpa only [inner_sum, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right] using h

end Cloning.BoundedOperator

namespace Cloning.MultimodeCoherent

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ}

/-- The scalar kernel dictated by the input and output Weyl cocycles. -/
def quantumPositiveKernel (f : (Fin d → ℂ) → ℂ) (r : ℝ)
    (a b : Fin d → ℂ) : ℂ :=
  displacementPhase (-a) b / displacementPhase (-(r • a)) (r • b) * f (b - a)

/-- Quantum positive-definiteness at the covariance scaling `r`. This tests
all finite phase-space configurations and all complex scalar coefficients. -/
def IsQuantumPositive (f : (Fin d → ℂ) → ℂ) (r : ℝ) : Prop :=
  ∀ n : ℕ, ∀ b : Fin n → (Fin d → ℂ), ∀ c : Fin n → ℂ,
    0 ≤ ∑ i, ∑ j, star (c i) * c j * quantumPositiveKernel f r (b i) (b j)

lemma displacement_inner_map_map (a : Fin d → ℂ) (x y : Fock d) :
    ⟪displacement a x, displacement a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (weylUnitary a).inner_map_map x y

/-- A matrix coefficient that removes the output Weyl Gram factor exactly. -/
lemma displaced_gram_coefficient (r : ℝ) (a b : Fin d → ℂ) (u : Fock d) :
    ⟪displacement (-(r • a)) u,
      displacement (r • (b - a)) (displacement (-(r • b)) u)⟫_ℂ =
    (displacementPhase (-(r • a)) (r • b))⁻¹ * ⟪u, u⟫_ℂ := by
  have hsum : -(r • a) + r • b = r • (b - a) := by
    rw [smul_sub]
    abel
  have h := congrArg (fun T : Fock d →L[ℂ] Fock d => T (displacement (-(r • b)) u))
    (displacement_comp (-(r • a)) (r • b))
  simp only [ContinuousLinearMap.comp_apply, displacement_cancel_neg,
    ContinuousLinearMap.smul_apply, hsum] at h
  have h' := congrArg (fun v : Fock d =>
    (displacementPhase (-(r • a)) (r • b))⁻¹ • v) h
  simp only [smul_smul, inv_mul_cancel₀ (displacementPhase_ne_zero _ _), one_smul] at h'
  rw [← h', inner_smul_right, displacement_inner_map_map]

/-- Every completely positive Weyl multiplier has the quantum-positive
kernel determined by the difference between its two Weyl cocycles. -/
theorem multiplier_isQuantumPositive
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d))
    (hCP : Cloning.BoundedOperator.IsCompletelyPositive Ψ)
    (r : ℝ) (f : (Fin d → ℂ) → ℂ)
    (hmult : ∀ b, Ψ (displacement b) = f b • displacement (r • b)) :
    IsQuantumPositive f r := by
  intro n b c
  have hgram := Cloning.BoundedOperator.gram_blockPositive (fun i : Fin n => displacement (b i))
  have h := hCP n _ hgram (fun i => c i •
    displacement (-(r • b i)) (coherentVector (0 : Fin d → ℂ)))
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [displacement_adjoint, displacement_comp]
  simp only [map_smul, hmult, ContinuousLinearMap.smul_apply, inner_smul_left,
    inner_smul_right]
  rw [show -b i + b j = b j - b i by abel, displaced_gram_coefficient]
  simp only [inner_self_eq_norm_sq_to_K, coherentVector_norm,
    RCLike.ofReal_eq_complex_ofReal, one_pow,
    Complex.ofReal_one, mul_one, quantumPositiveKernel, starRingEnd_apply, div_eq_mul_inv]
  ring

/-- Complete positivity and covariance yield the quantum-positive multiplier
without assuming a characteristic-function representation. -/
theorem covariant_weylMultiplier_isQuantumPositive
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d))
    (hCP : Cloning.BoundedOperator.IsCompletelyPositive Ψ) (r : ℝ)
    (hcov : ∀ (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d),
      ((displacement a).comp (Ψ A)).comp (displacement (-a)) =
        Ψ (((displacement (r • a)).comp A).comp (displacement (-(r • a))))) :
    IsQuantumPositive (weylMultiplier Ψ r) r :=
  multiplier_isQuantumPositive Ψ hCP r _ (covariant_linearMap_weyl_multiplier Ψ r hcov)

end Cloning.MultimodeCoherent
