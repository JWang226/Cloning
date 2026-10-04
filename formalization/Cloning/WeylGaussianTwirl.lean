import Cloning.WeylGaussianProjection
import Cloning.WeylGaussianTotalityScalar

/-! Gaussian-weighted translates of the abstract vacuum projection. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
open MeasureTheory Filter
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

private theorem continuous_phase_pair_totality :
    Continuous (fun ab : (Fin d → ℂ) × (Fin d → ℂ) => displacementPhase ab.1 ab.2) := by
  unfold displacementPhase Cloning.ComplexCoherent.displacementPhase
  fun_prop

def RegularWeyl.gaussianTwirlIntegrand (t : Fin d → ℝ) (v : H)
    (a z : Fin d → ℂ) : H :=
  ((gaussianWeight t a : ℂ)*(weylGaussianWeight z : ℂ)*
    displacementPhase a z*displacementPhase (a+z) (-a)) • W.operator z v

theorem RegularWeyl.integrable_gaussianTwirlIntegrand {t : Fin d → ℝ}
    (ht : ∀i,0<t i) (v : H) :
    Integrable (Function.uncurry (W.gaussianTwirlIntegrand t v)) (volume.prod volume) := by
  have hc : Continuous (Function.uncurry (W.gaussianTwirlIntegrand t v)) := by
    unfold RegularWeyl.gaussianTwirlIntegrand Function.uncurry
    apply Continuous.smul
    · exact ((((Complex.continuous_ofReal.comp (continuous_gaussianWeight t)).comp continuous_fst).mul
        ((Complex.continuous_ofReal.comp continuous_weylGaussianWeight).comp continuous_snd)).mul
        continuous_phase_pair_totality).mul
          (continuous_phase_pair_totality.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst.neg))
    · exact (W.continuous_apply v).comp continuous_snd
  apply (((integrable_gaussianWeight ht).mul_prod integrable_weylGaussianWeight).mul_const ‖v‖).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with az
  simp only [Function.uncurry, RegularWeyl.gaussianTwirlIntegrand, norm_smul, norm_mul,
    displacementPhase_norm, mul_one, W.operator_norm, Complex.norm_real,
    Real.norm_of_nonneg (weylGaussianWeight_nonneg _),
    Real.norm_of_nonneg (gaussianWeight_nonneg _ _)]
  exact le_rfl

private theorem operator_conjugation_totality (a z : Fin d → ℂ) (v : H) :
    W.operator a (W.operator z (W.operator (-a) v)) =
      (displacementPhase a z*displacementPhase (a+z) (-a)) • W.operator z v := by
  change W.toIsometry a (W.toIsometry z (W.toIsometry (-a) v)) = _
  rw [W.mul_apply a z, W.mul_apply (a+z) (-a), smul_smul]
  congr 2
  abel

/-- Integrating actual conjugates of the vacuum projection yields a narrower Gaussian average. -/
theorem RegularWeyl.gaussianProjection_twirl {t : Fin d → ℝ} (ht : ∀i,0<t i) (v : H) :
    (∫ a : Fin d → ℂ, (gaussianWeight t a : ℂ) •
      W.operator a (W.gaussianProjection (W.operator (-a) v))) =
      ((∏ i, Real.pi/t i : ℝ) : ℂ) •
        ∫ z : Fin d → ℂ, ((weylGaussianWeight z : ℂ)*
          (gaussianWeight (fun i => (t i)⁻¹) z : ℂ)) • W.operator z v := by
  let K := W.gaussianTwirlIntegrand t v
  have hexpand : (∫ a : Fin d → ℂ, (gaussianWeight t a : ℂ) •
      W.operator a (W.gaussianProjection (W.operator (-a) v))) = ∫ a, ∫ z, K a z := by
    apply integral_congr_ae
    filter_upwards [] with a
    have he := (W.operator a).integral_comp_comm (W.integrable_weighted_operator (W.operator (-a) v))
    change (∫ z, W.operator a ((weylGaussianWeight z : ℂ) • W.operator z (W.operator (-a) v))) =
      W.operator a (W.gaussianProjection (W.operator (-a) v)) at he
    rw [← he, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [map_smul, operator_conjugation_totality, smul_smul, K, RegularWeyl.gaussianTwirlIntegrand]
    congr 1
    ring
  rw [hexpand, integral_integral_swap (W.integrable_gaussianTwirlIntegrand ht v)]
  have he (a z : Fin d → ℂ) : K a z =
      (weylGaussianWeight z : ℂ) • (((gaussianWeight t a : ℂ)*
        displacementPhase a z*displacementPhase (a+z) (-a)) • W.operator z v) := by
    dsimp only [K, RegularWeyl.gaussianTwirlIntegrand]
    rw [smul_smul]
    congr 1
    ring
  change (∫ z, ∫ a, K a z) = _
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with z
  calc
    (∫ a, K a z) = ∫ a, (weylGaussianWeight z : ℂ) •
        (((gaussianWeight t a : ℂ)*displacementPhase a z*
          displacementPhase (a+z) (-a)) • W.operator z v) :=
      integral_congr_ae (Eventually.of_forall (fun a => he a z))
    _ = _ := by
      rw [integral_smul, integral_smul_const, integral_gaussian_conjugation_product ht]
      simp only [smul_smul]
      congr 1
      ring

end Cloning.WeylGNS
