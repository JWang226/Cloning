import Cloning.WeylIrreducible
import Cloning.WeylMultimodeContinuity
import Mathlib.MeasureTheory.Integral.Pi

/-! Scalar commutant for every finite number of bosonic modes. The vacuum
projector is derived as a Gaussian strong integral of the constructed Weyl
operators; irreducibility is not assumed as an input. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {d : ℕ}

/-- Product Gaussian weight with one factor `exp(-|aᵢ|²/2)/π` per mode. -/
def weylGaussianWeight (a : Fin d → ℂ) : ℝ :=
  ∏ i, ComplexCoherent.weylGaussianWeight (a i)

lemma weylGaussianWeight_nonneg (a : Fin d → ℂ) : 0 ≤ weylGaussianWeight a :=
  Finset.prod_nonneg (fun i _ ↦ ComplexCoherent.weylGaussianWeight_nonneg (a i))

lemma continuous_weylGaussianWeight : Continuous (weylGaussianWeight (d := d)) := by
  unfold weylGaussianWeight
  exact continuous_finset_prod _ (fun i _ ↦
    ComplexCoherent.continuous_weylGaussianWeight.comp (continuous_apply i))

lemma integrable_weylGaussianWeight : Integrable (weylGaussianWeight (d := d)) := by
  exact Integrable.fintype_prod (fun _ ↦ ComplexCoherent.integrable_weylGaussianWeight)

lemma integral_weylGaussianWeight : (∫ a : Fin d → ℂ, weylGaussianWeight a) = 2 ^ d := by
  change (∫ a : Fin d → ℂ, ∏ i, ComplexCoherent.weylGaussianWeight (a i)) = _
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (x : ℂ) ↦ ComplexCoherent.weylGaussianWeight x)]
  simp only [ComplexCoherent.integral_weylGaussianWeight, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

lemma integrable_weighted_displacement (v : Fock d) :
    Integrable (fun a : Fin d → ℂ ↦ (weylGaussianWeight a : ℂ) • displacement a v) := by
  apply (integrable_weylGaussianWeight.mul_const ‖v‖).mono'
    ((Complex.continuous_ofReal.comp continuous_weylGaussianWeight).smul
      (continuous_displacement v)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a ↦ by
    simp only [Function.comp_apply]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weylGaussianWeight_nonneg a), displacement_norm])

def weylGaussianVector (v : Fock d) : Fock d :=
  ∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) • displacement a v

lemma weylGaussianVector_norm (v : Fock d) : ‖weylGaussianVector v‖ ≤ 2 ^ d * ‖v‖ := by
  unfold weylGaussianVector
  calc
    _ ≤ ∫ a : Fin d → ℂ, ‖(weylGaussianWeight a : ℂ) • displacement a v‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ a : Fin d → ℂ, weylGaussianWeight a * ‖v‖ := by
      congr 1
      funext a
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weylGaussianWeight_nonneg a), displacement_norm]
    _ = _ := by rw [integral_mul_const, integral_weylGaussianWeight]

/-- A Gaussian strong integral gives a bounded map on the actual multimode
Fock space. -/
def weylGaussianAverage : Fock d →L[ℂ] Fock d :=
  ({ toFun := weylGaussianVector
     map_add' := by
       intro v w
       simp only [weylGaussianVector, map_add, smul_add]
       exact integral_add (integrable_weighted_displacement v) (integrable_weighted_displacement w)
     map_smul' := by
       intro c v
       simp only [weylGaussianVector, map_smul, smul_comm (weylGaussianWeight _ : ℂ) c,
         integral_smul, RingHom.id_apply] } : Fock d →ₗ[ℂ] Fock d).mkContinuous (2 ^ d)
           weylGaussianVector_norm

@[simp] lemma weylGaussianAverage_apply (v : Fock d) :
    weylGaussianAverage v =
      ∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) • displacement a v := rfl

lemma weighted_weyl_kernel (a z w : Fin d → ℂ) :
    (weylGaussianWeight a : ℂ) * ⟪coherentVector z, displacement a (coherentVector w)⟫_ℂ =
      ∏ i, (ComplexCoherent.weylGaussianWeight (a i) : ℂ) *
        ⟪ComplexCoherent.coherentVector (z i),
          ComplexCoherent.displacement (a i) (ComplexCoherent.coherentVector (w i))⟫_ℂ := by
  rw [displacement_coherentVector]
  simp only [weylGaussianWeight, inner_smul_right,
    coherentVector, inner_tensorVector, displacementPhase, Complex.ofReal_prod,
    ComplexCoherent.displacement_coherentVector, inner_smul_right,
    Pi.add_apply, ← Finset.prod_mul_distrib]

lemma integral_weighted_weyl_kernel (z w : Fin d → ℂ) :
    (∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) *
      ⟪coherentVector z, displacement a (coherentVector w)⟫_ℂ) =
      ⟪coherentVector z, coherentVector 0⟫_ℂ *
        ⟪coherentVector 0, coherentVector w⟫_ℂ := by
  simp_rw [weighted_weyl_kernel]
  rw [integral_fintype_prod_volume_eq_prod (f := fun (i : Fin d) (a : ℂ) ↦
    (ComplexCoherent.weylGaussianWeight a : ℂ) *
      ⟪ComplexCoherent.coherentVector (z i),
        ComplexCoherent.displacement a (ComplexCoherent.coherentVector (w i))⟫_ℂ)]
  simp only [ComplexCoherent.integral_weighted_weyl_kernel, Finset.prod_mul_distrib,
    coherentVector, inner_tensorVector, Pi.zero_apply]

/-- The product Gaussian strong integral equals the rank-one multimode vacuum
projection, for every finite number of modes, including zero. -/
theorem weylGaussianAverage_eq_vacuumProjector :
    weylGaussianAverage (d := d) =
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

lemma commutes_weylGaussianAverage (T : Fock d →L[ℂ] Fock d)
    (hT : ∀ a : Fin d → ℂ, T.comp (displacement a) = (displacement a).comp T) :
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
  exact congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L v) (hT a)

/-- The actual finite-multimode Weyl representation has scalar commutant. -/
theorem displacement_commutant_scalar (T : Fock d →L[ℂ] Fock d)
    (hT : ∀ a : Fin d → ℂ, T.comp (displacement a) = (displacement a).comp T) :
    T = ⟪coherentVector 0, T (coherentVector 0)⟫_ℂ • ContinuousLinearMap.id ℂ (Fock d) := by
  have hP := commutes_weylGaussianAverage T hT
  rw [weylGaussianAverage_eq_vacuumProjector] at hP
  have hv := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L (coherentVector 0)) hP
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    inner_self_eq_norm_sq_to_K, coherentVector_norm] at hv
  norm_num at hv
  apply continuousLinearMap_ext_coherent
  intro z
  have hz := congrArg (fun L : Fock d →L[ℂ] Fock d ↦ L (coherentVector 0)) (hT z)
  simp only [ContinuousLinearMap.comp_apply, displacement_vacuum] at hz
  conv_lhs => rw [hz, hv, map_smul, displacement_vacuum]
  rfl

theorem exists_scalar_of_commutes_displacement (T : Fock d →L[ℂ] Fock d)
    (hT : ∀ a : Fin d → ℂ, T.comp (displacement a) = (displacement a).comp T) :
    ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ (Fock d) :=
  ⟨_, displacement_commutant_scalar T hT⟩

end Cloning.MultimodeCoherent
