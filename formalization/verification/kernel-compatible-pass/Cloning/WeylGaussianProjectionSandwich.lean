import Cloning.WeylGaussianProjection

/-! The abstract Gaussian average is a projection and has the vacuum Weyl sandwich law. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
open MeasureTheory Filter
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

private theorem continuous_phase_pair :
    Continuous (fun ab : (Fin d → ℂ)×(Fin d → ℂ) ↦ displacementPhase ab.1 ab.2) := by
  unfold displacementPhase Cloning.ComplexCoherent.displacementPhase
  fun_prop

def RegularWeyl.gaussianSandwichIntegrand (z : Fin d → ℂ) (v : H)
    (a b : Fin d → ℂ) : H :=
  ((weylGaussianWeight a : ℂ)*(weylGaussianWeight b : ℂ)*
    displacementPhase a z*displacementPhase (a+z) b) • W.operator (a+z+b) v

set_option backward.isDefEq.respectTransparency true in
theorem RegularWeyl.integrable_gaussianSandwichIntegrand (z : Fin d → ℂ) (v : H) :
    Integrable (Function.uncurry (W.gaussianSandwichIntegrand z v)) (volume.prod volume) := by
  have hc1 : Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) ↦
      (weylGaussianWeight ab.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_weylGaussianWeight (d := d))).comp continuous_fst
  have hc2 : Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) ↦
      (weylGaussianWeight ab.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_weylGaussianWeight (d := d))).comp continuous_snd
  have hc3 : Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) ↦ displacementPhase ab.1 z) :=
    (continuous_displacementPhase z).comp continuous_fst
  have harg : Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) ↦ (ab.1 + z, ab.2)) :=
    (continuous_fst.add continuous_const).prodMk continuous_snd
  have hc4 : Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) ↦
      displacementPhase (ab.1 + z) ab.2) :=
    by
      have hh := (continuous_phase_pair (d := d)).comp harg
      exact hh
  have hc5 : Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) ↦
      W.operator (ab.1 + z + ab.2) v) :=
    (W.continuous_apply v).comp ((continuous_fst.add continuous_const).add continuous_snd)
  have hc : Continuous (Function.uncurry (W.gaussianSandwichIntegrand z v)) :=
    (((hc1.mul hc2).mul hc3).mul hc4).smul hc5
  apply ((integrable_weylGaussianWeight.mul_prod integrable_weylGaussianWeight).mul_const ‖v‖).mono' hc.aestronglyMeasurable
  filter_upwards [] with ab
  simp only [Function.uncurry, RegularWeyl.gaussianSandwichIntegrand, norm_smul, norm_mul,
    displacementPhase_norm, mul_one, W.operator_norm, Complex.norm_real,
    Real.norm_of_nonneg (weylGaussianWeight_nonneg _)]
  exact le_rfl

private theorem triple_operator (z a b : Fin d → ℂ) (v : H) :
    W.operator a (W.operator z (W.operator b v))=
      (displacementPhase a z*displacementPhase (a+z) b) • W.operator (a+z+b) v := by
  change W.toIsometry a (W.toIsometry z (W.toIsometry b v))=_
  rw [W.mul_apply a z, W.mul_apply (a+z) b, smul_smul]
  rfl

/-- The actual strong Gaussian average obeys the vacuum sandwich relation. -/
theorem RegularWeyl.gaussianProjection_sandwich_apply (z : Fin d → ℂ) (v : H) :
    W.gaussianProjection (W.operator z (W.gaussianProjection v))=
      (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) z : ℂ) • W.gaussianProjection v := by
  let K := W.gaussianSandwichIntegrand z v
  have hexpand : W.gaussianProjection (W.operator z (W.gaussianProjection v))=∫ a, ∫ b, K a b := by
    rw [W.gaussianProjection_apply]
    apply integral_congr_ae
    filter_upwards [] with a
    have he := ((W.operator a).comp (W.operator z)).integral_comp_comm (W.integrable_weighted_operator v)
    change (∫ b, W.operator a (W.operator z ((weylGaussianWeight b : ℂ) • W.operator b v)))=
      W.operator a (W.operator z (W.gaussianProjection v)) at he
    rw [← he, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with b
    simp only [map_smul, triple_operator, smul_smul, K, RegularWeyl.gaussianSandwichIntegrand]
    congr 1
    ring
  have hmp : MeasurePreserving (fun ac : (Fin d → ℂ)×(Fin d → ℂ) ↦ (ac.1,ac.2-z-ac.1))
      (volume.prod volume) (volume.prod volume) :=
    (measurePreserving_prod_sub volume volume).comp
      ((MeasurePreserving.id volume).prod (measurePreserving_sub_right volume z))
  have hi : Integrable (Function.uncurry (fun a c ↦ K a (c-z-a))) (volume.prod volume) :=
    hmp.integrable_comp_of_integrable (W.integrable_gaussianSandwichIntegrand z v)
  have hshift : (∫ a, ∫ b, K a b)=∫ a, ∫ c, K a (c-z-a) := by
    apply integral_congr_ae
    filter_upwards [] with a
    have he : (fun c ↦ K a (c-z-a))=(fun c ↦ K a (c-(z+a))) := by
      funext c
      congr 1
      abel
    rw [he, integral_sub_right_eq_self]
  rw [hexpand, hshift, integral_integral_swap hi]
  have he (a c : Fin d → ℂ) : K a (c-z-a)=
      ((weylGaussianWeight a : ℂ)*(weylGaussianWeight (c-z-a) : ℂ)*
        displacementPhase a z*displacementPhase (a+z) (c-z-a)) • W.operator c v := by
    dsimp only [K, RegularWeyl.gaussianSandwichIntegrand]
    congr 2
    abel
  simp_rw [he, integral_smul_const, integral_weylGaussian_sandwich, mul_smul]
  rw [integral_smul, W.gaussianProjection_apply]

theorem RegularWeyl.gaussianProjection_idempotent :
    W.gaussianProjection.comp W.gaussianProjection=W.gaussianProjection := by
  ext v
  have hh := W.gaussianProjection_sandwich_apply 0 v
  simpa only [W.operator_zero, ContinuousLinearMap.id_apply, gaussianWeight, Pi.zero_apply,
    norm_zero, zero_pow (by norm_num : (2:ℕ)≠0), mul_zero, neg_zero, Real.exp_zero,
    Finset.prod_const_one, Complex.ofReal_one, one_smul] using hh

end Cloning.WeylGNS
