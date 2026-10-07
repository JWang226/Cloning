import Cloning.WeylEigenoperators

/-! A covariant linear map on bounded Fock operators has a scalar Weyl
multiplier. This proves the algebraic part of the channel representation
argument. Complete positivity and normality are not needed for this part;
identifying its scalar multiplier with an idler state is a further theorem. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

variable {d : ℕ}

lemma displacementPhase_real_smul_left (r : ℝ) (a b : Fin d → ℂ) :
    displacementPhase (r • a) b = displacementPhase a (r • b) := by
  unfold displacementPhase
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.smul_apply, Complex.real_smul, ComplexCoherent.displacementPhase,
    map_mul, Complex.conj_ofReal]
  congr 1
  ring

lemma weylCharacter_real_smul_left (r : ℝ) (a b : Fin d → ℂ) :
    weylCharacter (r • a) b = weylCharacter a (r • b) := by
  unfold weylCharacter
  rw [displacementPhase_real_smul_left r a b,
    ← displacementPhase_real_smul_left r b a]

/-- Weyl operators are exact eigenoperators under Weyl conjugation. -/
theorem displacement_conjugation (a b : Fin d → ℂ) :
    ((displacement a).comp (displacement b)).comp (displacement (-a)) =
      weylCharacter a b • displacement b := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L (displacement (-a) v))
    (displacement_commutation a b)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    displacement_cancel_neg] using h

/-- The scalar multiplier selected by the actual vacuum matrix coefficient. -/
def weylMultiplier (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d))
    (r : ℝ) (b : Fin d → ℂ) : ℂ :=
  ⟪coherentVector (0 : Fin d → ℂ), Ψ (displacement b)
    (displacement (-(r • b)) (coherentVector (0 : Fin d → ℂ)))⟫_ℂ

/-- Abstract bounded-operator calculation, separated from the concrete Fock
instances to keep elaboration and kernel reduction inexpensive. -/
private theorem linearMap_covariance_eigenoperator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (W : (Fin d → ℂ) → H →L[ℂ] H) (χ : (Fin d → ℂ) → (Fin d → ℂ) → ℂ) (r : ℝ)
    (hconj : ∀ a b, ((W a).comp (W b)).comp (W (-a)) = χ a b • W b)
    (hinv : ∀ a v, W (-a) (W a v) = v)
    (hscale : ∀ a b, χ (r • a) b = χ a (r • b))
    (Ψ : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hΨ : ∀ a A, ((W a).comp (Ψ A)).comp (W (-a)) =
      Ψ (((W (r • a)).comp A).comp (W (-(r • a))))) (b : Fin d → ℂ) :
    ∀ a, (W a).comp (Ψ (W b)) = χ a (r • b) • (Ψ (W b)).comp (W a) := by
  intro a
  have ha := hΨ a (W b)
  have hright := hconj (r • a) b
  have hmap := Ψ.map_smul (χ (r • a) b) (W b)
  have hchar := congrArg (fun c : ℂ ↦ c • Ψ (W b)) (hscale a b)
  have ha' := ha.trans ((congrArg Ψ hright).trans (hmap.trans hchar))
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : H →L[ℂ] H ↦ L (W a v)) ha'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, hinv] using hv

/-- The Heisenberg action of every Weyl-covariant complex-linear operator map
is a scalar multiplier times the Weyl operator at the corresponding real
scaled frequency. All irreducibility inputs have been proved for this Fock
representation. -/
theorem covariant_linearMap_weyl_multiplier
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d)) (r : ℝ)
    (hΨ : ∀ (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d),
      ((displacement a).comp (Ψ A)).comp (displacement (-a)) =
        Ψ (((displacement (r • a)).comp A).comp (displacement (-(r • a)))))
    (b : Fin d → ℂ) :
    Ψ (displacement b) = weylMultiplier Ψ r b • displacement (r • b) := by
  unfold weylMultiplier
  exact eigenoperator_eq_scalar_displacement (Ψ (displacement b)) (r • b)
    (linearMap_covariance_eigenoperator displacement weylCharacter r
      displacement_conjugation displacement_neg_cancel (weylCharacter_real_smul_left r) Ψ hΨ b)

/-- Unitality normalizes the multiplier at zero. This follows for the actual
vacuum normalization and actual identity displacement. -/
theorem weylMultiplier_zero
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d)) (r : ℝ)
    (hΨ : Ψ (ContinuousLinearMap.id ℂ (Fock d)) = ContinuousLinearMap.id ℂ (Fock d)) :
    weylMultiplier Ψ r 0 = 1 := by
  have hz : r • (0 : Fin d → ℂ) = 0 := by ext i; simp
  rw [weylMultiplier, hz, neg_zero, displacement_zero, hΨ]
  simp only [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K, coherentVector_norm]
  norm_num

/-- An operator contraction has a Weyl multiplier of modulus at most one.
The contraction property is explicit here; deriving it from a particular
channel interface is separate from the algebraic multiplier theorem. -/
theorem weylMultiplier_norm_le_one
    (Ψ : (Fock d →L[ℂ] Fock d) →ₗ[ℂ] (Fock d →L[ℂ] Fock d)) (r : ℝ)
    (hcontract : ∀ A, ‖Ψ A‖ ≤ ‖A‖) (b : Fin d → ℂ) :
    ‖weylMultiplier Ψ r b‖ ≤ 1 := by
  unfold weylMultiplier
  have hD : ‖displacement b‖ ≤ 1 :=
    (displacement b).opNorm_le_bound zero_le_one (fun v ↦ by rw [displacement_norm b v, one_mul])
  calc
    _ ≤ ‖coherentVector (0 : Fin d → ℂ)‖ *
        ‖Ψ (displacement b) (displacement (-(r • b)) (coherentVector 0))‖ :=
      norm_inner_le_norm _ _
    _ = ‖Ψ (displacement b) (displacement (-(r • b)) (coherentVector 0))‖ := by
      rw [coherentVector_norm, one_mul]
    _ ≤ ‖Ψ (displacement b)‖ *
        ‖displacement (-(r • b)) (coherentVector 0)‖ :=
      (Ψ (displacement b)).le_opNorm _
    _ = ‖Ψ (displacement b)‖ := by rw [displacement_norm, coherentVector_norm, mul_one]
    _ ≤ ‖displacement b‖ := hcontract _
    _ ≤ 1 := hD

end Cloning.MultimodeCoherent
