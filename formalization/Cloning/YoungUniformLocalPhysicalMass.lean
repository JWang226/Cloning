import Cloning.TensorSchurDecompositionMultiplicity
import Cloning.YoungHookRatioLimit
import Cloning.YoungMultinomialLocal

/-! The exact physical Schur probability factors into the literal multinomial
mass, the proved hook correction, and the actual sector character ratio. -/

noncomputable section
open scoped BigOperators Topology Classical
namespace Cloning.YoungMultinomial
open Cloning.TensorLie Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Exact factorization for the physically constructed and normalized Young
measurement, with its representation multiplicities already discharged. -/
theorem tensorYoungPMF_eq_multinomial_character (d N : ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (μ : Shape d N)
    (hμ : Antitone (fun i ↦ (μ i).val)) (hN : ∑ i, (μ i).val = N) :
    (tensorYoungPMF N d p (fun i ↦ (hp i).le) hs μ).toReal =
      multinomialMass N p (fun i ↦ (μ i).val) *
        tableauCorrection (fun i ↦ (μ i).val) *
        (physicalSectorCharacter (fun i ↦ (μ i).val) p / (∏ i, p i ^ (μ i).val)) := by
  have hpw : (∏ i, p i ^ (μ i).val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ pow_ne_zero _ (hp i).ne')
  have hfac : (∏ i, ((μ i).val.factorial : ℝ)) ≠ 0 := by positivity
  rw [tensorYoungPMF_formula, standardCount_eq_multinomial_correction _ hμ hN,
    multinomialMass, Finset.prod_inv_distrib]
  field_simp

/-- The actual physical probability ratio isolates precisely the two proved
finite-dimensional corrections that accompany Stirling's Gaussian mass. -/
theorem tensorYoungPMF_div_gaussianMass (d N : ℕ) (p x : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (μ : Shape d N)
    (hμ : Antitone (fun i ↦ (μ i).val)) (hN : ∑ i, (μ i).val = N) :
    (tensorYoungPMF N d p (fun i ↦ (hp i).le) hs μ).toReal / gaussianMass N p x =
      (multinomialMass N p (fun i ↦ (μ i).val) / gaussianMass N p x) *
        tableauCorrection (fun i ↦ (μ i).val) *
        (physicalSectorCharacter (fun i ↦ (μ i).val) p / (∏ i, p i ^ (μ i).val)) := by
  rw [tensorYoungPMF_eq_multinomial_character d N p hp hs μ hμ hN]
  ring


/-- The root-indexed Bose partition product is exactly the reciprocal of the
finite hook correction limit. -/
theorem root_partition_product_eq_spectralCorrection_inv {d : ℕ} (p : Fin d → ℝ) :
    (∏ r : PositiveRoot d, (1 - p r.val.2 / p r.val.1)⁻¹) =
      (spectralCorrection p)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  rw [← Finset.prod_subtype (Finset.univ.filter (fun ij : Fin d × Fin d ↦ ij.1 < ij.2))
    (by simp) (fun ij : Fin d × Fin d ↦ 1 - p ij.2 / p ij.1)]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  unfold spectralCorrection
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

end Cloning.YoungMultinomial
