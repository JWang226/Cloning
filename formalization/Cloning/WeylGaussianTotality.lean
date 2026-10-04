import Cloning.WeylGaussianTwirl
import Cloning.WeylGaussianApproximation

/-! No vector can be orthogonal to every translate of the abstract Gaussian vacuum space. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
open MeasureTheory Filter
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

/-- The translated vacuum projections jointly separate vectors in every regular representation. -/
theorem RegularWeyl.eq_zero_of_projection_translates_zero (v : H)
    (hv : ∀ a : Fin d → ℂ, W.gaussianProjection (W.operator a v)=0) : v=0 := by
  apply W.eq_zero_of_gaussian_averages_zero v
  intro t ht
  let s : ℝ := (t-1/2)⁻¹
  have hs : 0<s := inv_pos.mpr (sub_pos.mpr ht)
  have h := W.gaussianProjection_twirl (t:=fun _ => s) (fun _ => hs) v
  simp only [hv, map_zero, smul_zero, integral_zero] at h
  have hc : (((∏ _i : Fin d, Real.pi/s : ℝ) : ℂ)) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (div_pos Real.pi_pos hs).ne'
  have hi := (smul_eq_zero.mp h.symm).resolve_left hc
  have hp : (((Real.pi^d : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ Real.pi_ne_zero)
  have he (a : Fin d → ℂ) :
      (weylGaussianWeight a : ℂ)*(gaussianWeight (fun _ : Fin d => s⁻¹) a : ℂ) =
        (((Real.pi^d : ℝ) : ℂ))⁻¹*(gaussianWeight (fun _ : Fin d => t) a : ℂ) := by
    rw [weylGaussianWeight_eq_gaussianWeight, Complex.ofReal_div]
    have hsum : ((fun _ : Fin d => (1/2:ℝ))+(fun _ : Fin d => s⁻¹))=(fun _ => t) := by
      funext i
      simp only [Pi.add_apply, s, inv_inv]
      ring
    have hm := gaussianWeight_mul (fun _ : Fin d => (1/2:ℝ)) (fun _ => s⁻¹) a
    rw [hsum] at hm
    calc
      _ = (((Real.pi^d : ℝ) : ℂ))⁻¹ *
          ((gaussianWeight (fun _ : Fin d => (1/2:ℝ)) a : ℂ) *
            (gaussianWeight (fun _ : Fin d => s⁻¹) a : ℂ)) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, hm]
  simp_rw [he, mul_smul] at hi
  rw [integral_smul] at hi
  exact (smul_eq_zero.mp hi).resolve_left (inv_ne_zero hp)

/-- Orthogonality to all displaced vectors in the Gaussian projection range forces zero. -/
theorem RegularWeyl.gaussianProjection_translates_total (v : H)
    (hv : ∀ (a : Fin d → ℂ) (x : H), ⟪W.operator a (W.gaussianProjection x),v⟫_ℂ=0) : v=0 := by
  apply W.eq_zero_of_projection_translates_zero v
  intro a
  apply ext_inner_left ℂ
  intro x
  rw [inner_zero_right]
  have hh := hv (-a) x
  rw [W.inner_operator, neg_neg, W.gaussianProjection_symmetric] at hh
  exact hh

end Cloning.WeylGNS
