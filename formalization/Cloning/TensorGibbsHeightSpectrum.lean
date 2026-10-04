import Cloning.TensorGibbsHeightBasis
import Cloning.TensorGibbsTail

/-! Each fixed physical height trace is eventually its exact finite bosonic
occupation sum. The trace identity follows from the constructed PBW basis. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

include hweight in
theorem tensorOperator_diagonal_normalizedLoweringWord (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (w : List (PositiveRoot d)) :
    tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ)))
      (normalizedLoweringWord Ω mu w) =
      (((∏ a, p a ^ mu a) * wordBoltzmann p w : ℝ) : ℂ) •
        normalizedLoweringWord Ω mu w := by
  rw [normalizedLoweringWord_eq_scale, map_smul,
    tensorOperator_diagonal_loweringWord Ω mu hweight p hp w]
  exact smul_comm _ _ _

theorem sectorGibbsOperator_height_invariant (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (H : ℕ) (x : cyclicSector Ω)
    (hx : x ∈ sectorHeightSpace Ω H) :
    sectorGibbsOperator Ω mu hweight hraise p x ∈ sectorHeightSpace Ω H := by
  change tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ))) x.val ∈ cyclicHeightSpace Ω H
  change x.val ∈ cyclicHeightSpace Ω H at hx
  suffices hh : ∀ y : TensorRegister n (Fin d), y ∈ cyclicHeightSpace Ω H →
      tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ))) y ∈ cyclicHeightSpace Ω H from hh x.val hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [tensorOperator_diagonal_loweringWord Ω mu hweight p hp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w,hw,rfl⟩)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def sectorHeightOperator (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (H : ℕ) :
    sectorHeightSpace Ω H →ₗ[ℂ] sectorHeightSpace Ω H :=
  (sectorGibbsOperator Ω mu hweight hraise p).toLinearMap.restrict
    (sectorGibbsOperator_height_invariant Ω mu hweight hraise p hp H)

theorem sectorHeightTrace_eq_trace (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (H : ℕ) :
    sectorHeightTrace Ω mu hweight hraise p H =
      (LinearMap.trace ℂ (sectorHeightSpace Ω H)
        (sectorHeightOperator Ω mu hweight hraise p hp H)).re := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ (sectorHeightSpace Ω H)), Complex.re_sum]
  rfl

theorem canonicalHeightBasis_gibbs (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (H : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d H =>
      normalizedLoweringWord Ω mu (canonicalWord k.val))) (k : ExactHeightOccupation d H) :
    sectorHeightOperator Ω mu hweight hraise p hp H (canonicalHeightBasis Ω mu H hgap hli k) =
      (((∏ a, p a ^ mu a) * wordBoltzmann p (canonicalWord k.val.val) : ℝ) : ℂ) •
        canonicalHeightBasis Ω mu H hgap hli k := by
  apply Subtype.ext
  apply Subtype.ext
  change tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ)))
      ((canonicalHeightBasis Ω mu H hgap hli k : cyclicSector Ω) : TensorRegister n (Fin d)) = _
  simp only [Submodule.coe_smul, canonicalHeightBasis_coe]
  exact tensorOperator_diagonal_normalizedLoweringWord Ω mu hweight p hp _

def bosonicHeightMass (p : Fin d → ℝ) (H : ℕ) : ℝ :=
  ∑ k : ExactHeightOccupation d H, wordBoltzmann p (canonicalWord k.val.val)

theorem sectorHeightMass_eq_bosonic (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (H : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d H =>
      normalizedLoweringWord Ω mu (canonicalWord k.val))) :
    sectorHeightMass Ω mu hweight hraise p H = bosonicHeightMass p H := by
  classical
  have hm : (∏ a, p a ^ mu a) ≠ 0 := (Finset.prod_pos (fun a _ => pow_pos (hp a) _)).ne'
  unfold sectorHeightMass
  rw [sectorHeightTrace_eq_trace Ω mu hweight hraise p hp H,
    LinearMap.trace_eq_matrix_trace ℂ (canonicalHeightBasis Ω mu H hgap hli)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, canonicalHeightBasis_gibbs,
    map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one, Complex.re_sum, Complex.ofReal_re]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hm]
  rfl

end Cloning.TensorLie
