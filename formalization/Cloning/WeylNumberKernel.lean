import Cloning.WeylMultimodeContinuity
import Cloning.MultimodeCoherentGaussianMixture
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RealDeriv

/-! Exact coherent/number matrix elements of the constructed Weyl operator. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A single factor of the exact coherent/number displacement kernel. -/
def numberKernel (a z : ℂ) (k : ℕ) : ℂ :=
  Complex.exp (-(starRingEnd ℂ z * z) / 2 - (starRingEnd ℂ a * a) / 2 +
    starRingEnd ℂ z * a) * (starRingEnd ℂ z - starRingEnd ℂ a) ^ k /
      (Real.sqrt (k.factorial : ℝ) : ℂ)

theorem numberKernel_eq_coherent (a z : ℂ) (k : ℕ) :
    numberKernel a z k =
      starRingEnd ℂ (ComplexCoherent.displacementPhase (-a) z) *
        starRingEnd ℂ (ComplexCoherent.coherentVector (-a + z) k) := by
  rw [ComplexCoherent.coherentVector_apply, ComplexCoherent.displacementPhase]
  simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.ofReal_exp]
  rw [numberKernel]
  have he : starRingEnd ℂ (((-a) * starRingEnd ℂ z - starRingEnd ℂ (-a) * z) / 2) +
      ((-‖-a + z‖ ^ 2 / 2 : ℝ) : ℂ) =
      -(starRingEnd ℂ z * z) / 2 - (starRingEnd ℂ a * a) / 2 + starRingEnd ℂ z * a := by
    push_cast
    simp only [map_div₀, map_sub, map_mul, map_neg, map_ofNat,
      starRingEnd_self_apply, ComplexCoherent.norm_sq_cast, map_add]
    ring
  rw [← he, Complex.exp_add]
  simp only [map_add, map_neg, map_div₀, map_sub, map_mul, map_ofNat,
    starRingEnd_self_apply]
  ring

theorem inner_coherent_displacement_number {d : ℕ}
    (a z : Fin d → ℂ) (k : Fin d → ℕ) :
    ⟪coherentVector z, displacement a (numberBasis d k)⟫_ℂ =
      ∏ i, numberKernel (a i) (z i) (k i) := by
  have h := (weylUnitary (-a)).inner_map_map (coherentVector z)
    (displacement a (numberBasis d k))
  simp only [weylUnitary_apply, displacement_neg_cancel] at h
  rw [← h, displacement_coherentVector, inner_smul_left,
    ← inner_conj_symm (coherentVector (-a + z)) (numberBasis d k), inner_numberBasis,
    coherentVector_coefficients]
  simp only [displacementPhase, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [numberKernel_eq_coherent, ComplexCoherent.coherentVector_apply]
  rfl

end Cloning.MultimodeCoherent
