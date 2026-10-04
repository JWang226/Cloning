import Cloning.PCTFlatGaussianCrossReduction
import Cloning.PCTProjectorPurityGaussianCross

/-! The actual flat reduced-state differential has the stated Gaussian
cross exponential moment. Both integrability and the exact value are proved
for the literal purification-frame tangent, independently of that frame. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTFlatGaussianCross
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] {s : ℕ}

/-- Integrability is obtained from the actual identified Gaussian law. -/
theorem flat_cross_integrable
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hH0 : ∀ a b,star (u 0 (b,a))=u 0 (a,b))
    (r : ℕ) (hr : 0<r) {δ : ℝ} (hδ : 0<δ) (hδ2 : δ<1/2) :
    Integrable (fun z => Real.exp ((r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.1) *
       partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.2))).re))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) :=
  (integrable_flat_cross_iff_real_coordinates u hH0 r hr hδ).mpr
    (PCTProjectorPurity.integrable_exp_re_cross s hδ hδ2)

/-- Exact full cross moment, with no assumed Gaussian coordinate law. -/
theorem flat_cross_integral
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hH0 : ∀ a b,star (u 0 (b,a))=u 0 (a,b))
    (r : ℕ) (hr : 0<r) {δ : ℝ} (hδ : 0<δ) (hδ2 : δ<1/2) :
    (∫ z, Real.exp ((r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.1) *
       partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.2))).re)
      ∂(gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ)))=
      (1-4*δ^2)^(-(s : ℝ)/2) := by
  rw [integral_flat_cross_eq_real_coordinates u hH0 r hr hδ]
  exact PCTProjectorPurity.integral_exp_re_cross s hδ hδ2

/-- The rank-r physical reference gives exactly r²−1 real Hermitian tangent
directions. The dimension and Hermitian reference are derived from the supplied
actual orthonormal purification frame. -/
theorem schmidt_flat_cross_moment {r : ℕ} (hr : 0<r)
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (Fin r×Fin r)))
    (h0 : u 0=coefficientVector (schmidtCoefficients (fun _ : Fin r => (r : ℝ)⁻¹)))
    {δ : ℝ} (hδ : 0<δ) (hδ2 : δ<1/2) :
    Integrable (fun z => Real.exp ((r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : Fin r => (r : ℝ)⁻¹) (frameTangentMatrix u z.1) *
       partialTraceDifferential (fun _ : Fin r => (r : ℝ)⁻¹) (frameTangentMatrix u z.2))).re))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) ∧
    (∫ z, Real.exp ((r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : Fin r => (r : ℝ)⁻¹) (frameTangentMatrix u z.1) *
       partialTraceDifferential (fun _ : Fin r => (r : ℝ)⁻¹) (frameTangentMatrix u z.2))).re)
      ∂(gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ)))=
      (1-4*δ^2)^(-((r : ℝ)^2-1)/2) := by
  have hH0 := schmidt_reference_hermitian u _ h0
  refine ⟨flat_cross_integrable u hH0 r hr hδ hδ2,?_⟩
  rw [flat_cross_integral u hH0 r hr hδ hδ2]
  have hn : r^2=s+1 := by simpa using frame_card_sq u
  have hnR : (r : ℝ)^2=(s : ℝ)+1 := by exact_mod_cast hn
  congr 1
  linarith

end Cloning.PCTFlatGaussianCross
