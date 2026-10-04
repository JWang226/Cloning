import Cloning.WeylGaussianTwistedConvolution

/-! Exact Gaussian sandwich convolution for the standard Weyl cocycle.
These scalar identities apply to every strongly continuous Weyl representation. -/
noncomputable section
open scoped BigOperators Topology ComplexOrder
open MeasureTheory
namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The scalar convolution underlying `P W(z) P = exp(-|z|²/2) P`. -/
theorem integral_gaussian_sandwich_single (z c : ℂ) :
    (∫ a : ℂ, (Real.exp (-‖a‖^2/2) : ℂ) *
      (Real.exp (-‖c-z-a‖^2/2) : ℂ) *
      displacementPhase a z * displacementPhase (a+z) (c-z-a)) =
      (Real.pi : ℂ) * (Real.exp (-‖z‖^2/2) : ℂ) * (Real.exp (-‖c‖^2/2) : ℂ) := by
  let C : ℂ := -((‖c-z‖^2 : ℝ) : ℂ)/2+
    (z*starRingEnd ℂ (c-z)-starRingEnd ℂ z*(c-z))/2
  have he (a : ℂ) : (Real.exp (-‖a‖^2/2) : ℂ) *
      (Real.exp (-‖c-z-a‖^2/2) : ℂ) *
      displacementPhase a z * displacementPhase (a+z) (c-z-a) =
      Complex.exp C * Complex.exp (-((‖a‖^2 : ℝ) : ℂ)+starRingEnd ℂ c*a+(-z)*starRingEnd ℂ a) := by
    simp only [Complex.ofReal_exp, displacementPhase, ← Complex.exp_add]
    congr 1
    simp only [C, norm_sq_cast', map_sub, map_add, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_complex_gaussian_linear]
  rw [mul_left_comm, ← Complex.exp_add]
  simp only [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  simp only [C, norm_sq_cast', map_sub, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

end Cloning.ComplexCoherent

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Product Gaussian sandwich identity in an arbitrary finite number of modes. -/
theorem integral_gaussian_sandwich_product (z c : Fin d → ℂ) :
    (∫ a, (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) a : ℂ) *
      (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) (c-z-a) : ℂ) *
      displacementPhase a z * displacementPhase (a+z) (c-z-a)) =
      (Real.pi : ℂ)^d * (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) z : ℂ) *
        (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) c : ℂ) := by
  have hhalf (t : ℝ) : -(1/2:ℝ)*t = -t/2 := by ring
  have he (a : Fin d → ℂ) : (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) a : ℂ) *
      (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) (c-z-a) : ℂ) *
      displacementPhase a z * displacementPhase (a+z) (c-z-a) =
      ∏ i, ((Real.exp (-‖a i‖^2/2) : ℂ) * (Real.exp (-‖c i-z i-a i‖^2/2) : ℂ) *
        Cloning.ComplexCoherent.displacementPhase (a i) (z i) *
        Cloning.ComplexCoherent.displacementPhase (a i+z i) (c i-z i-a i)) := by
    simp only [gaussianWeight, displacementPhase, Complex.ofReal_prod, Pi.sub_apply,
      Pi.add_apply, Finset.prod_mul_distrib, hhalf]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod (fun i (a : ℂ) ↦
    (Real.exp (-‖a‖^2/2) : ℂ) * (Real.exp (-‖c i-z i-a‖^2/2) : ℂ) *
      Cloning.ComplexCoherent.displacementPhase a (z i) *
      Cloning.ComplexCoherent.displacementPhase (a+z i) (c i-z i-a))]
  simp only [Cloning.ComplexCoherent.integral_gaussian_sandwich_single,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    gaussianWeight, Complex.ofReal_prod, hhalf]

end Cloning.MultimodeCoherent
