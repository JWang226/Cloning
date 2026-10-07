import Cloning.WeylGNSRegular
import Cloning.WeylGaussianSandwichNormalized
import Mathlib.MeasureTheory.Function.L2Space

/-! The Gaussian strong average of every regular Weyl representation. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
open MeasureTheory Filter
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

theorem RegularWeyl.integrable_weighted_operator (v : H) :
    Integrable (fun a : Fin d → ℂ ↦ (weylGaussianWeight a : ℂ) • W.operator a v) := by
  apply (integrable_weylGaussianWeight.mul_const ‖v‖).mono'
    ((Complex.continuous_ofReal.comp continuous_weylGaussianWeight).smul
      (W.continuous_apply v)).aestronglyMeasurable
  exact Eventually.of_forall (fun a ↦ by
    change ‖(weylGaussianWeight a : ℂ) • W.operator a v‖ ≤ weylGaussianWeight a*‖v‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weylGaussianWeight_nonneg a), W.operator_norm])

def RegularWeyl.gaussianVector (v : H) : H :=
  ∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) • W.operator a v

theorem RegularWeyl.gaussianVector_norm (v : H) : ‖W.gaussianVector v‖ ≤ 2^d*‖v‖ := by
  unfold RegularWeyl.gaussianVector
  calc
    _ ≤ ∫ a : Fin d → ℂ, ‖(weylGaussianWeight a : ℂ) • W.operator a v‖ := norm_integral_le_integral_norm _
    _ = ∫ a : Fin d → ℂ, weylGaussianWeight a*‖v‖ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weylGaussianWeight_nonneg a), W.operator_norm]
    _ = _ := by rw [integral_mul_const, integral_weylGaussianWeight]

/-- Gaussian averaging uses strong vector integrals, without operator-norm continuity. -/
def RegularWeyl.gaussianProjection : H →L[ℂ] H :=
  ({ toFun := W.gaussianVector
     map_add' := by
       intro v w
       simp only [RegularWeyl.gaussianVector, map_add, smul_add]
       exact integral_add (W.integrable_weighted_operator v) (W.integrable_weighted_operator w)
     map_smul' := by
       intro c v
       simp only [RegularWeyl.gaussianVector, map_smul, smul_comm (weylGaussianWeight _ : ℂ) c,
         integral_smul, RingHom.id_apply] } : H →ₗ[ℂ] H).mkContinuous (2^d) W.gaussianVector_norm

@[simp] theorem RegularWeyl.gaussianProjection_apply (v : H) :
    W.gaussianProjection v=∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ) • W.operator a v := rfl

theorem RegularWeyl.inner_operator (a : Fin d → ℂ) (v w : H) :
    ⟪W.operator a v,w⟫_ℂ=⟪v,W.operator (-a) w⟫_ℂ := by
  have hh := (W.toIsometry a).inner_map_map v (W.operator (-a) w)
  rw [RegularWeyl.operator_apply, W.mul_apply, displacementPhase_neg_right,
    add_neg_cancel, W.zero_apply, one_smul] at hh
  exact hh

private theorem integral_inner_left {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → H} (hf : Integrable f μ) (v : H) :
    (∫ x, ⟪f x,v⟫_ℂ ∂μ)=⟪∫ x, f x ∂μ,v⟫_ℂ := by
  calc
    _ = ∫ x, star ⟪v,f x⟫_ℂ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x ↦ (inner_conj_symm (f x) v).symm)
    _ = star (∫ x, ⟪v,f x⟫_ℂ ∂μ) := integral_conj
    _ = _ := by rw [integral_inner hf]; exact inner_conj_symm _ _

theorem RegularWeyl.gaussianProjection_symmetric (v w : H) :
    ⟪W.gaussianProjection v,w⟫_ℂ=⟪v,W.gaussianProjection w⟫_ℂ := by
  rw [W.gaussianProjection_apply, W.gaussianProjection_apply,
    ← integral_inner_left (W.integrable_weighted_operator v), ← integral_inner (W.integrable_weighted_operator w)]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal, W.inner_operator]
  have he : (∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ)*⟪v,W.operator (-a) w⟫_ℂ)=
      ∫ a : Fin d → ℂ, (weylGaussianWeight a : ℂ)*⟪v,W.operator a w⟫_ℂ := by
    have hh := integral_neg_eq_self (fun a : Fin d → ℂ ↦ (weylGaussianWeight a : ℂ)*⟪v,W.operator a w⟫_ℂ) volume
    simpa only [weylGaussianWeight_neg] using hh
  exact he

theorem RegularWeyl.gaussianProjection_selfAdjoint : IsSelfAdjoint W.gaussianProjection :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr W.gaussianProjection_symmetric

end Cloning.WeylGNS
