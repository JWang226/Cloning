import Cloning.PCTFlatGaussianCrossKernel
import Cloning.PCTFlatGaussianCrossLaw

/-! Reduction of the physical flat-state cross integral to independent real
Gaussian coordinates, including equivalence of Bochner integrability. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTFlatGaussianCross
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] {s : ℕ}

local instance flatReductionRegisterFinite : FiniteDimensional ℂ (Register (A×A)) :=
  (registerBasis (A×A)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

lemma frame_card_sq (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A))) :
    Fintype.card A^2=s+1 := by
  have h := Module.finrank_eq_card_basis u.toBasis
  rw [Module.finrank_eq_card_basis (registerBasis (A×A)).toOrthonormalBasis.toBasis] at h
  simpa [pow_two] using h

lemma schmidt_reference_hermitian
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (p : A → ℝ) (h0 : u 0=coefficientVector (schmidtCoefficients p)) :
    ∀ a b,star (u 0 (b,a))=u 0 (a,b) := by
  intro a b
  rw [h0]
  by_cases hab : a=b
  · subst b
    simp [coefficientVector_apply,schmidtCoefficients]
  · simp [coefficientVector_apply,schmidtCoefficients,hab,Ne.symm hab]

def flatCrossExponential (r : ℕ) (v : Register (A×A) × Register (A×A)) : ℝ :=
  Real.exp ((r : ℝ)*(Matrix.trace
    (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (fun a b => v.1 (a,b)) *
     partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (fun a b => v.2 (a,b)))).re)

lemma continuous_flatCrossExponential (r : ℕ) : Continuous (flatCrossExponential (A := A) r) := by
  have heval (a b : A) : Continuous (fun x : Register (A×A) => x (a,b)) := by
    simpa only [registerBasis_apply,register_inner_single] using
      (continuous_const.inner continuous_id : Continuous (fun x : Register (A×A) =>
        ⟪registerBasis (A×A) (a,b),x⟫_ℂ))
  have hfst (a b : A) : Continuous (fun x : Register (A×A) × Register (A×A) => x.1 (a,b)) :=
    (heval a b).comp continuous_fst
  have hsnd (a b : A) : Continuous (fun x : Register (A×A) × Register (A×A) => x.2 (a,b)) :=
    (heval a b).comp continuous_snd
  unfold flatCrossExponential partialTraceDifferential
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.add_apply,
    Matrix.conjTranspose_apply]
  fun_prop

lemma flatCrossExponential_frameTangent (r : ℕ)
    (u : Fin (s+1) → Register (A×A)) (z w : Fin s → ℂ) :
    flatCrossExponential r (frameTangent u z,frameTangent u w)=
      Real.exp ((r : ℝ)*(Matrix.trace
        (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z) *
         partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u w))).re) := rfl

/-- Every continuous cross integral is transported through an actual
Hermitian frame with exactly the same reference vector. -/
theorem integral_flat_cross_eq_real_coordinates
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hH0 : ∀ a b,star (u 0 (b,a))=u 0 (a,b))
    (r : ℕ) (hr : 0<r) {δ : ℝ} (hδ : 0<δ) :
    (∫ z, Real.exp ((r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.1) *
       partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.2))).re)
      ∂(gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ)))=
    ∫ z, Real.exp (4*∑ i,(z.1 i).re*(z.2 i).re)
      ∂(gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ)) := by
  obtain ⟨v,hv0,hv⟩ := exists_hermitian_frame (frame_card_sq u) (u 0)
    (u.orthonormal.norm_eq_one 0) hH0
  have he := integral_frameTangent_prod_eq u v hv0.symm hδ
    (flatCrossExponential r) (continuous_flatCrossExponential r)
  simp only [flatCrossExponential_frameTangent] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [flatDifferential_rank_trace_cross v hv r hr]

/-- The physical exponential is integrable exactly when the derived real
coordinate expression is. Thus no integrability is silently presumed. -/
theorem integrable_flat_cross_iff_real_coordinates
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hH0 : ∀ a b,star (u 0 (b,a))=u 0 (a,b))
    (r : ℕ) (hr : 0<r) {δ : ℝ} (hδ : 0<δ) :
    Integrable (fun z => Real.exp ((r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.1) *
       partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z.2))).re))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) ↔
    Integrable (fun z => Real.exp (4*∑ i,(z.1 i).re*(z.2 i).re))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) := by
  obtain ⟨v,hv0,hv⟩ := exists_hermitian_frame (frame_card_sq u) (u 0)
    (u.orthonormal.norm_eq_one 0) hH0
  have he := integrable_frameTangent_prod_iff u v hv0.symm hδ
    (flatCrossExponential r) (continuous_flatCrossExponential r)
  simp only [flatCrossExponential_frameTangent] at he
  rw [he]
  have hf : (fun z : (Fin s → ℂ) × (Fin s → ℂ) =>
      Real.exp ((r : ℝ)*(Matrix.trace
        (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix v z.1) *
         partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix v z.2))).re))=
      (fun z => Real.exp (4*∑ i,(z.1 i).re*(z.2 i).re)) := by
    funext z
    rw [flatDifferential_rank_trace_cross v hv r hr]
  rw [hf]

end Cloning.PCTFlatGaussianCross
