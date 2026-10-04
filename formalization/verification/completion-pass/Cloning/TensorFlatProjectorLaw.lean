import Cloning.TensorSchurDecompositionMultiplicity
import Cloning.TensorSchurDecompositionConcentration
import Cloning.WeylCharacterDimensionPhysical
import Cloning.YoungGeneralMoments

/-! The actual flat-spectrum sector state and physical Young law. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.YoungGeneral
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Scalar one-particle input acts by its actual tensor degree. -/
theorem sectorGibbsOperator_const
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) (c : ℝ) :
    sectorGibbsOperator Ω mu hweight hraise (fun _ => c) =
      ((c ^ n : ℝ) : ℂ) • (1 : cyclicSector Ω →L[ℂ] cyclicSector Ω) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply lp.ext
  funext w
  change tensorOperator n (Matrix.diagonal (fun _ : Fin d => (c : ℂ)))
    (x : TensorRegister n (Fin d)) w = ((c ^ n : ℝ) : ℂ) * (x : TensorRegister n (Fin d)) w
  rw [tensorOperator_diagonal_apply]
  simp

/-- The flat partition function is the literal sector dimension. -/
theorem sectorPartitionFunction_const
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (c : ℝ) (hc : 0 ≤ c) :
    sectorPartitionFunction Ω mu hweight hraise (fun _ => c) =
      c ^ n * (Module.finrank ℂ (cyclicSector Ω) : ℝ) := by
  rw [sectorPartitionFunction_eq_linearMapTrace Ω mu hweight hraise _ (fun _ => hc),
    sectorGibbsOperator_const]
  change (LinearMap.trace ℂ _ (((c ^ n : ℝ) : ℂ) •
    (LinearMap.id : cyclicSector Ω →ₗ[ℂ] cyclicSector Ω))).re = _
  rw [map_smul, LinearMap.trace_id]
  simp only [smul_eq_mul]
  norm_cast

/-- The actual normalized flat sector density is maximally mixed. -/
theorem sectorGibbsState_flat_op
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (hΩ : ‖Ω‖ = 1)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) (hd : 0 < d) :
    (sectorGibbsState Ω mu hweight hraise hΩ (flatSpectrum d)
      (fun _ => by unfold flatSpectrum; positivity)).op =
      (((Module.finrank ℂ (cyclicSector Ω) : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
  have hc : 0 < (1 / (d : ℝ)) := by positivity
  change (((sectorPartitionFunction Ω mu hweight hraise (fun _ => 1 / (d : ℝ)))⁻¹ : ℝ) : ℂ) •
    sectorGibbsOperator Ω mu hweight hraise (fun _ => 1 / (d : ℝ)) = _
  rw [sectorPartitionFunction_const Ω mu hweight hraise _ hc.le,
    sectorGibbsOperator_const, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_pos hc n).ne', mul_one]

/-- The physical Young law of the maximally mixed state on `ℂ^d`. -/
def tensorFlatYoungPMF (n d : ℕ) (hd : 0 < d) : PMF (Shape d n) :=
  tensorYoungPMF n d (flatSpectrum d) (fun _ => by unfold flatSpectrum; positivity)
    (flatSpectrum_sum d hd)

/-- Exact physical flat label mass: multiplicity times actual dimension,
divided by the tensor dimension. -/
theorem tensorFlatYoungPMF_formula (n d : ℕ) (hd : 0 < d) (mu : Shape d n)
    (hmu : Antitone (fun a => (mu a).val)) (hsum : ∑ a, (mu a).val = n) :
    (tensorFlatYoungPMF n d hd mu).toReal =
      (standardCount n (fun a => (mu a).val) : ℝ) *
        (partitionDimension (fun a => (mu a).val) hmu : ℝ) / (d : ℝ) ^ n := by
  rw [tensorFlatYoungPMF, tensorYoungPMF_formula]
  simp only [physicalSectorCharacter, dif_pos hmu]
  rw [show flatSpectrum d = (fun _ => 1 / (d : ℝ)) from rfl,
    sectorPartitionFunction_const _ _ _ _ _ (by positivity)]
  change _ * ((1 / (d : ℝ)) ^ (∑ a, (mu a).val) *
    (partitionDimension (fun a => (mu a).val) hmu : ℝ)) = _
  rw [hsum, one_div_pow]
  ring

/-- The same exact label law in the Weyl product coordinates. -/
theorem tensorFlatYoungPMF_weyl (n d : ℕ) (hd : 0 < d) (mu : Shape d n)
    (hmu : Antitone (fun a => (mu a).val)) (hsum : ∑ a, (mu a).val = n) :
    (tensorFlatYoungPMF n d hd mu).toReal =
      (standardCount n (fun a => (mu a).val) : ℝ) *
        Cloning.WeylCharacter.dimensionProduct (fun a => (mu a).val) / (d : ℝ) ^ n := by
  rw [tensorFlatYoungPMF_formula n d hd mu hmu hsum, partitionDimension_eq_dimensionProduct]

end Cloning.TensorLie
