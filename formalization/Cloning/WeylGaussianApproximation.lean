import Cloning.WeylGaussianProjection
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Strong Gaussian approximate identities for arbitrary regular Weyl representations. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
open MeasureTheory Filter
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

/-- Strong continuity and a fixed integrable Gaussian give a genuine approximate identity. -/
theorem RegularWeyl.gaussian_average_tendsto (v : H) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a : Fin d → ℂ,
      (gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • W.operator (ε n • a) v)
      atTop (𝓝 (((Real.pi^d : ℝ) : ℂ) • v)) := by
  have hg := integrable_gaussianWeight (d:=d) (fun _ => zero_lt_one)
  have hc (n : ℕ) : Continuous (fun a : Fin d → ℂ =>
      (gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • W.operator (ε n • a) v) :=
    (Complex.continuous_ofReal.comp (continuous_gaussianWeight _)).smul
      ((W.continuous_apply v).comp (continuous_const_smul (ε n)))
  have hb (n : ℕ) : ∀ᵐ a : Fin d → ℂ,
      ‖(gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • W.operator (ε n • a) v‖ ≤
        gaussianWeight (fun _ => (1:ℝ)) a * ‖v‖ := by
    filter_upwards [] with a
    simp only [norm_smul, W.operator_norm, Complex.norm_real,
      Real.norm_of_nonneg (gaussianWeight_nonneg _ _)]
    exact le_rfl
  have hl : ∀ᵐ a : Fin d → ℂ,
      Tendsto (fun n => (gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • W.operator (ε n • a) v)
        atTop (𝓝 ((gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • v)) := by
    filter_upwards [] with a
    have harg : Tendsto (fun n => ε n • a) atTop (𝓝 (0 : Fin d → ℂ)) := by
      simpa only [zero_smul] using hε.smul_const a
    have hw := ((W.continuous_apply v).tendsto 0).comp harg
    have he : W.toIsometry 0 v = v := W.zero_apply v
    simpa only [RegularWeyl.operator_apply, he] using
      tendsto_const_nhds.smul hw
  have ht := tendsto_integral_of_dominated_convergence
    (fun a : Fin d → ℂ => gaussianWeight (fun _ => (1:ℝ)) a * ‖v‖)
    (fun n => (hc n).aestronglyMeasurable) (hg.mul_const ‖v‖) hb hl
  have he : (∫ a : Fin d → ℂ, (gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • v) =
      (((Real.pi^d : ℝ) : ℂ) • v) := by
    rw [integral_smul_const, integral_complex_ofReal, integral_gaussianWeight (fun _ => zero_lt_one)]
    simp
  simpa only [he] using ht

/-- Vanishing of all sufficiently concentrated Gaussian averages forces the vector to vanish. -/
theorem RegularWeyl.eq_zero_of_gaussian_averages_zero (v : H)
    (hz : ∀ t : ℝ, (1/2:ℝ)<t →
      (∫ a : Fin d → ℂ, (gaussianWeight (fun _ => t) a : ℂ) • W.operator a v)=0) : v=0 := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he (n : ℕ) : (∫ a : Fin d → ℂ,
      (gaussianWeight (fun _ => (1:ℝ)) a : ℂ) • W.operator (ε n • a) v)=0 := by
    have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
    have ht : (1/2:ℝ)<((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have hs := Measure.integral_comp_smul volume
      (fun a : Fin d → ℂ => (gaussianWeight (fun _ => ((n:ℝ)+1)^2) a : ℂ) • W.operator a v) (ε n)
    rw [hz _ ht, smul_zero] at hs
    have hw (a : Fin d → ℂ) : gaussianWeight (fun _ => ((n:ℝ)+1)^2) (ε n • a) =
        gaussianWeight (fun _ => (1:ℝ)) a := by
      unfold gaussianWeight
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, ε,
        abs_of_pos (inv_pos.mpr hn)]
      field_simp
    simpa only [hw] using hs
  have ht := W.gaussian_average_tendsto v ε hε
  simp_rw [he] at ht
  have heq : (0:H)=((Real.pi^d : ℝ) : ℂ) • v := tendsto_nhds_unique tendsto_const_nhds ht
  exact (smul_eq_zero.mp heq.symm).resolve_left
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ Real.pi_ne_zero))

end Cloning.WeylGNS
