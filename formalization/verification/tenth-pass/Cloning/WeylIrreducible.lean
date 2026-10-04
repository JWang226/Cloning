import Cloning.WeylIrreducibleAverage

/-! The commutant of the constructed Fock Weyl representation is scalar.
A proved Gaussian strong integral yields the rank-one vacuum projection. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

lemma weighted_weyl_kernel (a z w : ℂ) :
    (weylGaussianWeight a : ℂ) * ⟪coherentVector z, displacement a (coherentVector w)⟫_ℂ =
      (⟪coherentVector z, coherentVector w⟫_ℂ / (Real.pi : ℂ)) *
        Complex.exp (-((‖a‖ ^ 2 : ℝ) : ℂ) + starRingEnd ℂ z * a + (-w) * starRingEnd ℂ a) := by
  rw [displacement_coherentVector, inner_smul_right]
  simp only [weylGaussianWeight, Complex.ofReal_div, Complex.ofReal_exp,
    displacementPhase, inner_coherentVector]
  have h : ((-‖a‖ ^ 2 / 2 : ℝ) : ℂ) +
      ((a * starRingEnd ℂ w - starRingEnd ℂ a * w) / 2) +
      (((-(‖z‖ ^ 2 + ‖a + w‖ ^ 2) / 2 : ℝ) : ℂ) + starRingEnd ℂ z * (a + w)) =
      (((-(‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 : ℝ) : ℂ) + starRingEnd ℂ z * w) +
      (-((‖a‖ ^ 2 : ℝ) : ℂ) + starRingEnd ℂ z * a + (-w) * starRingEnd ℂ a) := by
    push_cast
    simp only [norm_sq_cast, map_add]
    ring
  field_simp
  simp only [← Complex.exp_add]
  congr 1
  push_cast at h ⊢
  linear_combination h

lemma integral_weighted_weyl_kernel (z w : ℂ) :
    (∫ a : ℂ, (weylGaussianWeight a : ℂ) *
      ⟪coherentVector z, displacement a (coherentVector w)⟫_ℂ) =
      ⟪coherentVector z, coherentVector 0⟫_ℂ *
        ⟪coherentVector 0, coherentVector w⟫_ℂ := by
  simp_rw [weighted_weyl_kernel]
  rw [integral_const_mul, integral_complex_gaussian_linear]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_mul_eq_mul_div]
  rw [show ⟪coherentVector z, coherentVector w⟫_ℂ *
      ((Real.pi : ℂ) * Complex.exp (starRingEnd ℂ z * -w)) / Real.pi =
      ⟪coherentVector z, coherentVector w⟫_ℂ * Complex.exp (starRingEnd ℂ z * -w) by
        field_simp]
  simp only [inner_coherentVector_factorized]
  simp only [norm_zero, sq, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one,
    map_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, one_mul]
  rw [mul_assoc, ← Complex.exp_add]
  have he : starRingEnd ℂ z * w + starRingEnd ℂ z * -w = 0 := by ring
  rw [he, Complex.exp_zero, mul_one]

/-- The vacuum projection is a strong Gaussian integral of the actual Weyl
operators, with the normalization `exp(-|a|²/2)/π`. -/
theorem weylGaussianAverage_eq_vacuumProjector :
    weylGaussianAverage =
      InnerProductSpace.rankOne ℂ (coherentVector 0) (coherentVector 0) := by
  apply continuousLinearMap_ext_coherent
  intro w
  apply sub_eq_zero.mp
  apply coherentVector_total
  intro z
  rw [inner_sub_right]
  apply sub_eq_zero.mpr
  have hi := (innerSL ℂ (coherentVector z)).integral_comp_comm
    (integrable_weighted_displacement (coherentVector w))
  simp only [innerSL_apply_apply, inner_smul_right] at hi
  rw [weylGaussianAverage_apply, ← hi, integral_weighted_weyl_kernel,
    InnerProductSpace.rankOne_apply, inner_smul_right]
  exact mul_comm _ _

/-- Every bounded operator in the Weyl commutant commutes with the Gaussian
average, by functoriality of the actual vector-valued Bochner integral. -/
lemma commutes_weylGaussianAverage (T : Fock →L[ℂ] Fock)
    (hT : ∀ a : ℂ, T.comp (displacement a) = (displacement a).comp T) :
    T.comp weylGaussianAverage = weylGaussianAverage.comp T := by
  apply ContinuousLinearMap.ext
  intro v
  change T (weylGaussianAverage v) = weylGaussianAverage (T v)
  rw [weylGaussianAverage_apply, weylGaussianAverage_apply,
    ← T.integral_comp_comm (integrable_weighted_displacement v)]
  congr 1
  funext a
  rw [map_smul]
  congr 1
  exact congrArg (fun L : Fock →L[ℂ] Fock ↦ L v) (hT a)

/-- The constructed one-mode Weyl representation has scalar commutant.
The proof derives the vacuum projection from Weyl operators, then uses the
proved cyclicity of the vacuum. -/
theorem displacement_commutant_scalar (T : Fock →L[ℂ] Fock)
    (hT : ∀ a : ℂ, T.comp (displacement a) = (displacement a).comp T) :
    T = ⟪coherentVector 0, T (coherentVector 0)⟫_ℂ • ContinuousLinearMap.id ℂ Fock := by
  have hP := commutes_weylGaussianAverage T hT
  rw [weylGaussianAverage_eq_vacuumProjector] at hP
  have hv := congrArg (fun L : Fock →L[ℂ] Fock ↦ L (coherentVector 0)) hP
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    inner_self_eq_norm_sq_to_K, coherentVector_norm] at hv
  norm_num at hv
  apply continuousLinearMap_ext_coherent
  intro z
  have hz := congrArg (fun L : Fock →L[ℂ] Fock ↦ L (coherentVector 0)) (hT z)
  simp only [ContinuousLinearMap.comp_apply, displacement_vacuum] at hz
  conv_lhs => rw [hz, hv, map_smul, displacement_vacuum]
  rfl

/-- Existence formulation of the exact scalar-commutant conclusion. -/
theorem exists_scalar_of_commutes_displacement (T : Fock →L[ℂ] Fock)
    (hT : ∀ a : ℂ, T.comp (displacement a) = (displacement a).comp T) :
    ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ Fock :=
  ⟨_, displacement_commutant_scalar T hT⟩

end Cloning.ComplexCoherent
