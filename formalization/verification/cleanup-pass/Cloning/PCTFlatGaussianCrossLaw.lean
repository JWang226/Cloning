import Cloning.PCTGaussianCovariance
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The actual circular Gaussian tangent law depends only on the reference
vector, not on the orthonormal frame used to integrate it. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTFlatGaussianCross
open Cloning.PCT Cloning.PCTGaussianCovariance Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {C : Type*} [Fintype C] [DecidableEq C] {s : ℕ}

local instance flatLawRegisterMeasurable : MeasurableSpace (Register C) := borel _
local instance flatLawRegisterBorel : BorelSpace (Register C) := ⟨rfl⟩

local instance flatLawRegisterComplexFinite : FiniteDimensional ℂ (Register C) :=
  (registerBasis C).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
local instance flatLawRegisterRealFinite : FiniteDimensional ℝ (Register C) :=
  Module.Finite.trans ℂ (Register C)

lemma register_real_inner (x y : Register C) : ⟪x,y⟫_ℝ=(⟪x,y⟫_ℂ).re := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  simp only [tsum_fintype,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_eq_re_inner (𝕜 := ℂ) (x i) (y i)

lemma continuous_frameTangent (u : Fin (s+1) → Register C) : Continuous (frameTangent u) := by
  unfold frameTangent
  fun_prop

private def dualTest (L : StrongDual ℝ (Register C)) : Register C :=
  (-Complex.I/2) • (InnerProductSpace.toDual ℝ (Register C)).symm L

private lemma dualTest_phase (L : StrongDual ℝ (Register C)) (x : Register C) :
    ⟪dualTest L,x⟫_ℂ-⟪x,dualTest L⟫_ℂ=(L x : ℂ)*Complex.I := by
  let y := (InnerProductSpace.toDual ℝ (Register C)).symm L
  have hL : (⟪y,x⟫_ℂ).re=L x := by
    rw [← register_real_inner]
    exact InnerProductSpace.toDual_symm_apply
  change ⟪(-Complex.I/2) • y,x⟫_ℂ-⟪x,(-Complex.I/2) • y⟫_ℂ=_
  have hxy : ⟪x,y⟫_ℂ=star ⟪y,x⟫_ℂ := (inner_conj_symm x y).symm
  rw [inner_smul_left,inner_smul_right,hxy]
  have hscalar (c : ℂ) : star (-Complex.I/2)*c-(-Complex.I/2)*star c=
      (c.re : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [Complex.star_def,Complex.mul_re,Complex.mul_im] <;> ring
  simp only [starRingEnd_apply]
  rw [hscalar,hL]

/-- Equality of actual pushforward measures, proved by all continuous real
linear characteristic functionals and the projected-norm formula. -/
theorem frameTangent_map_eq
    (u v : OrthonormalBasis (Fin (s+1)) ℂ (Register C)) (h0 : u 0=v 0)
    {δ : ℝ} (hδ : 0<δ) :
    (gaussianProductMeasure (fun _ : Fin s => δ)).map (frameTangent u)=
      (gaussianProductMeasure (fun _ : Fin s => δ)).map (frameTangent v) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hδ)
  have hu : AEMeasurable (frameTangent u) (gaussianProductMeasure (fun _ : Fin s => δ)) :=
    (continuous_frameTangent u).aemeasurable
  have hv : AEMeasurable (frameTangent v) (gaussianProductMeasure (fun _ : Fin s => δ)) :=
    (continuous_frameTangent v).aemeasurable
  letI := Measure.isProbabilityMeasure_map hu
  letI := Measure.isProbabilityMeasure_map hv
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,
    integral_map hu (by fun_prop),integral_map hv (by fun_prop)]
  simp_rw [← dualTest_phase]
  rw [frameTangent_characteristic u hδ,frameTangent_characteristic v hδ,h0]

/-- The two independent physical tangents have the same actual product
pushforward in every frame through the same reference. -/
theorem frameTangent_prod_map_eq
    (u v : OrthonormalBasis (Fin (s+1)) ℂ (Register C)) (h0 : u 0=v 0)
    {δ : ℝ} (hδ : 0<δ) :
    ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
      (gaussianProductMeasure (fun _ : Fin s => δ))).map
        (Prod.map (frameTangent u) (frameTangent u))=
    ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
      (gaussianProductMeasure (fun _ : Fin s => δ))).map
        (Prod.map (frameTangent v) (frameTangent v)) := by
  letI := gaussianProductMeasure_probability (fun _ : Fin s => hδ)
  rw [← Measure.map_prod_map _ _ (continuous_frameTangent u).measurable
    (continuous_frameTangent u).measurable,
    ← Measure.map_prod_map _ _ (continuous_frameTangent v).measurable
      (continuous_frameTangent v).measurable,frameTangent_map_eq u v h0 hδ]

theorem integral_frameTangent_prod_eq
    (u v : OrthonormalBasis (Fin (s+1)) ℂ (Register C)) (h0 : u 0=v 0)
    {δ : ℝ} (hδ : 0<δ) (f : Register C × Register C → ℝ) (hf : Continuous f) :
    (∫ z, f (frameTangent u z.1,frameTangent u z.2)
      ∂(gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ)))=
    ∫ z, f (frameTangent v z.1,frameTangent v z.2)
      ∂(gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ)) := by
  have hu := (continuous_frameTangent u).prodMap (continuous_frameTangent u)
  have hv := (continuous_frameTangent v).prodMap (continuous_frameTangent v)
  change (∫ z, f (Prod.map (frameTangent u) (frameTangent u) z) ∂_)=_
  rw [← integral_map hu.aemeasurable hf.aestronglyMeasurable,
    frameTangent_prod_map_eq u v h0 hδ,
    integral_map hv.aemeasurable hf.aestronglyMeasurable]
  rfl

theorem integrable_frameTangent_prod_iff
    (u v : OrthonormalBasis (Fin (s+1)) ℂ (Register C)) (h0 : u 0=v 0)
    {δ : ℝ} (hδ : 0<δ) (f : Register C × Register C → ℝ) (hf : Continuous f) :
    Integrable (fun z => f (frameTangent u z.1,frameTangent u z.2))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) ↔
    Integrable (fun z => f (frameTangent v z.1,frameTangent v z.2))
      ((gaussianProductMeasure (fun _ : Fin s => δ)).prod
        (gaussianProductMeasure (fun _ : Fin s => δ))) := by
  have hu := (continuous_frameTangent u).prodMap (continuous_frameTangent u)
  have hv := (continuous_frameTangent v).prodMap (continuous_frameTangent v)
  change Integrable (f ∘ Prod.map (frameTangent u) (frameTangent u)) _ ↔
    Integrable (f ∘ Prod.map (frameTangent v) (frameTangent v)) _
  rw [← integrable_map_measure hf.aestronglyMeasurable hu.aemeasurable,
    frameTangent_prod_map_eq u v h0 hδ,
    integrable_map_measure hf.aestronglyMeasurable hv.aemeasurable]

end Cloning.PCTFlatGaussianCross
