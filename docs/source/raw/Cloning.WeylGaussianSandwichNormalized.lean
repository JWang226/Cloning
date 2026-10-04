import Cloning.WeylGaussianSandwich
import Cloning.WeylIrreducibleMultimode

/-! The sandwich convolution in the normalized vacuum-projector weight. -/
noncomputable section
open scoped BigOperators Topology ComplexOrder
open MeasureTheory
namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {d : ℕ}

theorem weylGaussianWeight_eq_gaussianWeight (a : Fin d → ℂ) :
    weylGaussianWeight a=gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) a/(Real.pi^d) := by
  simp only [weylGaussianWeight, ComplexCoherent.weylGaussianWeight,
    gaussianWeight, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

@[simp] theorem weylGaussianWeight_neg (a : Fin d → ℂ) :
    weylGaussianWeight (-a)=weylGaussianWeight a := by
  simp [weylGaussianWeight, ComplexCoherent.weylGaussianWeight]

theorem integral_weylGaussian_sandwich (z c : Fin d → ℂ) :
    (∫ a, (weylGaussianWeight a : ℂ)*(weylGaussianWeight (c-z-a) : ℂ)*
      displacementPhase a z*displacementPhase (a+z) (c-z-a)) =
      (gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ)) z : ℂ)*(weylGaussianWeight c : ℂ) := by
  let G := gaussianWeight (fun _ : Fin d ↦ (1/2:ℝ))
  let q : ℂ := (Real.pi : ℂ)^d
  have hq : q≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have he (a : Fin d → ℂ) : (weylGaussianWeight a : ℂ)*(weylGaussianWeight (c-z-a) : ℂ)*
      displacementPhase a z*displacementPhase (a+z) (c-z-a) =
      (q*q)⁻¹*((G a : ℂ)*(G (c-z-a) : ℂ)*displacementPhase a z*displacementPhase (a+z) (c-z-a)) := by
    simp only [weylGaussianWeight_eq_gaussianWeight, Complex.ofReal_div, Complex.ofReal_pow]
    dsimp only [q, G]
    field_simp
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian_sandwich_product,
    weylGaussianWeight_eq_gaussianWeight, Complex.ofReal_div, Complex.ofReal_pow]
  change (q*q)⁻¹*(q*(G z : ℂ)*(G c : ℂ))=(G z : ℂ)*((G c : ℂ)/q)
  field_simp

end Cloning.MultimodeCoherent
