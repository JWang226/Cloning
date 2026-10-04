import Cloning.HeisenbergDualContinuity

/-! Actual channel Weyl multipliers for arbitrary real diagonal amplitude gains.
The multiplier is extracted from the vacuum coefficient of the constructed
Heisenberg dual. No characteristic-function representation is assumed. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

variable {d : ℕ}

/-- Coordinatewise real amplitude scaling of phase space. -/
def diagonalScale (r : Fin d → ℝ) (a : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (r i : ℂ) * a i

@[simp] theorem diagonalScale_zero (r : Fin d → ℝ) : diagonalScale r 0 = 0 := by
  ext i
  simp [diagonalScale]

@[simp] theorem diagonalScale_neg (r : Fin d → ℝ) (a : Fin d → ℂ) :
    diagonalScale r (-a) = -diagonalScale r a := by
  ext i
  simp [diagonalScale]

@[simp] theorem diagonalScale_sub (r : Fin d → ℝ) (a b : Fin d → ℂ) :
    diagonalScale r (a - b) = diagonalScale r a - diagonalScale r b := by
  ext i
  simp [diagonalScale, mul_sub]

@[simp] theorem diagonalScale_star (r : Fin d → ℝ) (a : Fin d → ℂ) :
    diagonalScale r (star a) = star (diagonalScale r a) := by
  ext i
  simp [diagonalScale]

theorem continuous_diagonalScale (r : Fin d → ℝ) : Continuous (diagonalScale r) :=
  continuous_pi (fun i => continuous_const.mul (continuous_apply i))

lemma displacementPhase_diagonalScale_left (r : Fin d → ℝ) (a b : Fin d → ℂ) :
    displacementPhase (diagonalScale r a) b =
      displacementPhase a (diagonalScale r b) := by
  unfold displacementPhase
  apply Finset.prod_congr rfl
  intro i _
  simp only [diagonalScale, ComplexCoherent.displacementPhase, map_mul, Complex.conj_ofReal]
  congr 1
  ring

lemma weylCharacter_diagonalScale_left (r : Fin d → ℝ) (a b : Fin d → ℂ) :
    weylCharacter (diagonalScale r a) b = weylCharacter a (diagonalScale r b) := by
  unfold weylCharacter
  rw [displacementPhase_diagonalScale_left,
    ← displacementPhase_diagonalScale_left r b a]

/-- The actual vacuum coefficient, with independent amplitude gains. -/
def diagonalWeylMultiplier
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d))
    (r : Fin d → ℝ) (b : Fin d → ℂ) : ℂ :=
  ⟪coherentVector (0 : Fin d → ℂ), Ψ (displacement b)
    (displacement (-(diagonalScale r b)) (coherentVector 0))⟫_ℂ

private theorem diagonal_covariance_eigenoperator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (W : (Fin d → ℂ) → H →L[ℂ] H) (χ : (Fin d → ℂ) → (Fin d → ℂ) → ℂ)
    (S : (Fin d → ℂ) → (Fin d → ℂ))
    (hconj : ∀ a b, ((W a).comp (W b)).comp (W (-a)) = χ a b • W b)
    (hinv : ∀ a v, W (-a) (W a v) = v)
    (hscale : ∀ a b, χ (S a) b = χ a (S b))
    (Ψ : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hΨ : ∀ a A, ((W a).comp (Ψ A)).comp (W (-a)) =
      Ψ (((W (S a)).comp A).comp (W (-(S a))))) (b : Fin d → ℂ) :
    ∀ a, (W a).comp (Ψ (W b)) = χ a (S b) • (Ψ (W b)).comp (W a) := by
  intro a
  have ha := hΨ a (W b)
  have hright := hconj (S a) b
  have hmap := Ψ.map_smul (χ (S a) b) (W b)
  have hchar := congrArg (fun c : ℂ => c • Ψ (W b)) (hscale a b)
  have ha' := ha.trans ((congrArg Ψ hright).trans (hmap.trans hchar))
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : H →L[ℂ] H => L (W a v)) ha'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, hinv] using hv

/-- Diagonal displacement covariance forces an actual scalar multiplier. -/
theorem diagonal_covariant_linearMap_weyl_multiplier
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d)) (r : Fin d → ℝ)
    (hΨ : ∀ (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d),
      ((displacement a).comp (Ψ A)).comp (displacement (-a)) =
        Ψ (((displacement (diagonalScale r a)).comp A).comp
          (displacement (-(diagonalScale r a))))) (b : Fin d → ℂ) :
    Ψ (displacement b) = diagonalWeylMultiplier Ψ r b •
      displacement (diagonalScale r b) := by
  unfold diagonalWeylMultiplier
  exact eigenoperator_eq_scalar_displacement (Ψ (displacement b)) (diagonalScale r b)
    (diagonal_covariance_eigenoperator displacement weylCharacter (diagonalScale r)
      displacement_conjugation displacement_neg_cancel
      (weylCharacter_diagonalScale_left r) Ψ hΨ b)

theorem diagonalWeylMultiplier_zero
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d)) (r : Fin d → ℝ)
    (hΨ : Ψ (ContinuousLinearMap.id ℂ (Fock d)) = ContinuousLinearMap.id ℂ (Fock d)) :
    diagonalWeylMultiplier Ψ r 0 = 1 := by
  rw [diagonalWeylMultiplier, diagonalScale_zero, neg_zero, displacement_zero, hΨ]
  simp only [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K, coherentVector_norm]
  norm_num

/-- Schrödinger covariance passes to the actual normal dual. -/
theorem heisenbergDual_diagonal_weyl_covariance
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : Fin d → ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale r a) (Φ T))
    (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d) :
    ((displacement a).comp (heisenbergDual Φ A)).comp (displacement (-a)) =
      heisenbergDual Φ (((displacement (diagonalScale r a)).comp A).comp
        (displacement (-(diagonalScale r a)))) := by
  have hcov : ∀ T, Φ (sandwichCLM (displacement (-a))
      (star (displacement (-a))) T) =
      sandwichCLM (displacement (diagonalScale r (-a)))
        (star (displacement (diagonalScale r (-a)))) (Φ T) := by
    intro T
    simpa only [displacementTraceMap, ContinuousLinearMap.star_eq_adjoint,
      displacement_adjoint] using hΦ (-a) T
  have h := heisenbergDual_covariance Φ (displacement (-a))
    (displacement (diagonalScale r (-a))) hcov A
  simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
    neg_neg, diagonalScale_neg, ContinuousLinearMap.mul_def] using h

theorem traceClass_diagonal_weyl_multiplier
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : Fin d → ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale r a) (Φ T)) (b : Fin d → ℂ) :
    heisenbergDual Φ (displacement b) =
      diagonalWeylMultiplier (heisenbergDual Φ) r b • displacement (diagonalScale r b) :=
  diagonal_covariant_linearMap_weyl_multiplier (heisenbergDual Φ) r
    (heisenbergDual_diagonal_weyl_covariance Φ r hΦ) b

/-- Continuity follows from the nonvanishing vacuum Gaussian and normality. -/
theorem continuous_traceClass_diagonalWeylMultiplier
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : Fin d → ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale r a) (Φ T)) :
    Continuous (diagonalWeylMultiplier (heisenbergDual Φ) r) := by
  have heq (b : Fin d → ℂ) : diagonalWeylMultiplier (heisenbergDual Φ) r b =
      tracePairing (Φ (coherentProjector 0)) (displacement b) /
        ⟪coherentVector 0, displacement (diagonalScale r b) (coherentVector 0)⟫_ℂ := by
    apply (eq_div_iff (vacuum_characteristic_ne_zero (diagonalScale r b))).mpr
    have h := congrArg (fun A : Fock d →L[ℂ] Fock d =>
      ⟪coherentVector 0, A (coherentVector 0)⟫_ℂ)
      (traceClass_diagonal_weyl_multiplier Φ r hΦ b)
    simpa only [heisenbergDual_inner, ContinuousLinearMap.smul_apply,
      inner_smul_right] using h.symm
  rw [funext heq]
  apply (continuous_tracePairing_displacement (Φ (coherentProjector 0))).div
  · exact continuous_const.inner
      ((continuous_displacement (coherentVector 0)).comp (continuous_diagonalScale r))
  · exact fun b => vacuum_characteristic_ne_zero (diagonalScale r b)

/-- The normalized multiplier is constructed for the supplied physical channel. -/
theorem quantumChannel_diagonal_weyl_multiplier
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : Fin d → ℝ)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (diagonalScale r a) (Φ.toLinearMap T)) :
    (∀ b, Φ.heisenberg (displacement b) =
      diagonalWeylMultiplier Φ.heisenberg r b • displacement (diagonalScale r b)) ∧
      diagonalWeylMultiplier Φ.heisenberg r 0 = 1 ∧
      Continuous (diagonalWeylMultiplier Φ.heisenberg r) := by
  exact ⟨traceClass_diagonal_weyl_multiplier
    Φ.toPositiveTracePreservingMap.toContinuousLinearMap r hΦ,
    diagonalWeylMultiplier_zero Φ.heisenberg r Φ.heisenberg_unital,
    continuous_traceClass_diagonalWeylMultiplier
      Φ.toPositiveTracePreservingMap.toContinuousLinearMap r hΦ⟩

end Cloning.MultimodeCoherent
