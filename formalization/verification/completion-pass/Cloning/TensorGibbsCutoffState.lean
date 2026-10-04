import Cloning.TensorGibbsTruncation
import Cloning.TensorGibbsPartitionLimit

/-! Exact Gibbs eigenvalues in the common physical cutoff frame, and the
literal trace-norm residual after finite occupation truncation. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

def sectorGibbsDensity (p : Fin d → ℝ) : TraceClass (cyclicSector Ω) :=
  (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) •
    sectorGibbsWeight Ω mu hweight hraise p

@[simp] theorem sectorGibbsDensity_coe (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    (sectorGibbsDensity Ω mu hweight hraise p).1 =
      (sectorGibbsState Ω mu hweight hraise hΩ p hp).op := rfl

theorem sectorGibbsDensity_nonneg (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    0 ≤ (sectorGibbsDensity Ω mu hweight hraise p).1 :=
  (sectorGibbsState Ω mu hweight hraise hΩ p hp).positive

theorem sectorGibbsDensity_trace (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) :
    traceCLM (sectorGibbsDensity Ω mu hweight hraise p) = 1 :=
  (sectorGibbsState Ω mu hweight hraise hΩ p hp).trace_one

def sectorOccupationWeight (p : Fin d → ℝ) (k : PositiveRoot d → ℕ) : ℝ :=
  (∏ a, p a ^ mu a) / sectorPartitionFunction Ω mu hweight hraise p *
    wordBoltzmann p (canonicalWord k)

theorem sectorGibbsOperator_cutoffFrame (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (R : ℕ) (i : CutoffIndex d R) :
    sectorGibbsOperator Ω mu hweight hraise p (cutoffSectorFrame Ω mu R i) =
      (((∏ a, p a ^ mu a) * wordBoltzmann p (cutoffWord d R i) : ℝ) : ℂ) •
        cutoffSectorFrame Ω mu R i := by
  apply Subtype.ext
  have h := tensorOperator_diagonal_weight (fun a => (p a : ℂ)) (cutoffFrame Ω mu R i)
    (fun a => (mu a : ℤ) + loweringWeight (cutoffWord d R i) a) (fun a => by
      simpa only [Int.cast_add, Int.cast_natCast] using cutoffFrame_cartan Ω mu R hweight i a)
  have hc : (∏ a, (p a : ℂ) ^ ((mu a : ℤ) + loweringWeight (cutoffWord d R i) a)) =
      (((∏ a, p a ^ mu a) * wordBoltzmann p (cutoffWord d R i) : ℝ) : ℂ) := by
    rw [← shiftedWeight_boltzmann p (fun a => (hp a).ne') mu (cutoffWord d R i)]
    simp only [Complex.ofReal_prod, Complex.ofReal_zpow]
  rw [hc] at h
  exact h

theorem sectorGibbsDensity_cutoffFrame (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (R : ℕ) (i : CutoffIndex d R) :
    (sectorGibbsDensity Ω mu hweight hraise p).1 (cutoffSectorFrame Ω mu R i) =
      (sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val : ℂ) •
        cutoffSectorFrame Ω mu R i := by
  change (((sectorPartitionFunction Ω mu hweight hraise p)⁻¹ : ℝ) : ℂ) •
    sectorGibbsOperator Ω mu hweight hraise p (cutoffSectorFrame Ω mu R i) = _
  rw [sectorGibbsOperator_cutoffFrame Ω mu hweight hraise p hp]
  simp only [sectorOccupationWeight, cutoffWord, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_inv, smul_smul, div_eq_mul_inv]
  congr 1
  ring

theorem cutoffSectorFrame_orthonormal (R : ℕ)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) :
    Orthonormal ℂ (cutoffSectorFrame Ω mu R) := by
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪cutoffFrame Ω mu R i, cutoffFrame Ω mu R j⟫_ℂ = _
  exact orthonormal_iff_ite.mp (gramSchmidtNormed_orthonormal (𝕜 := ℂ) hli) i j

def sectorGibbsCutoff (p : Fin d → ℝ) (R : ℕ) : TraceClass (cyclicSector Ω) :=
  frameMatrix (cutoffSectorFrame Ω mu R)
    (Matrix.diagonal (fun i => (sectorOccupationWeight Ω mu hweight hraise p
      (cutoffOccupation d R i).val : ℂ)))

theorem sectorGibbsCutoff_residual_nonneg (hΩ : ‖Ω‖ = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) :
    0 ≤ (sectorGibbsDensity Ω mu hweight hraise p - sectorGibbsCutoff Ω mu hweight hraise p R).1 :=
  spectralFrame_residual_nonneg _ (sectorGibbsDensity_nonneg Ω mu hweight hraise hΩ p hp)
    _ (cutoffSectorFrame_orthonormal Ω mu R hli) _
    (sectorGibbsDensity_cutoffFrame Ω mu hweight hraise p hp R)

theorem sectorGibbsCutoff_error (hΩ : ‖Ω‖ = 1)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ)
    (hli : LinearIndependent ℂ (cutoffRawFrame Ω mu R)) :
    ‖sectorGibbsDensity Ω mu hweight hraise p - sectorGibbsCutoff Ω mu hweight hraise p R‖ =
      1 - ∑ i : CutoffIndex d R,
        sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val := by
  rw [sectorGibbsCutoff, spectralFrame_residual_norm _
    (sectorGibbsDensity_nonneg Ω mu hweight hraise hΩ p hp) _
    (cutoffSectorFrame_orthonormal Ω mu R hli) _
    (sectorGibbsDensity_cutoffFrame Ω mu hweight hraise p hp R),
    sectorGibbsDensity_trace Ω mu hweight hraise hΩ p hp, Complex.one_re]

end Cloning.TensorLie
