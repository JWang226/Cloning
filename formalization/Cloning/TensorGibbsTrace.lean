import Cloning.TensorGibbsHeight
import Mathlib.Analysis.InnerProductSpace.Trace

/-! The actual partition function decomposes into orthogonal height traces.
Polynomial height multiplicities and literal operator bounds control each
term. These are traces of the physical sector, not a supplied character law. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

abbrev SectorHeightIndex (Ω : TensorRegister n (Fin d)) :=
  Σ H : ℕ, Fin (Module.finrank ℂ (sectorHeightSpace Ω H))

def sectorHeightFrame (Ω : TensorRegister n (Fin d)) (i : SectorHeightIndex Ω) : cyclicSector Ω :=
  (stdOrthonormalBasis ℂ (sectorHeightSpace Ω i.1) i.2 : cyclicSector Ω)

theorem sectorHeightFrame_orthonormal
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    Orthonormal ℂ (sectorHeightFrame Ω) := by
  constructor
  · intro i
    exact (stdOrthonormalBasis ℂ (sectorHeightSpace Ω i.1)).norm_eq_one i.2
  · rintro ⟨H,i⟩ ⟨J,j⟩ hij
    by_cases h : H = J
    · subst J
      apply (stdOrthonormalBasis ℂ (sectorHeightSpace Ω H)).inner_eq_zero
      intro he
      apply hij
      cases he
      rfl
    · exact cyclicHeightSpace_isOrtho Ω mu hweight (Ne.symm h)
        (stdOrthonormalBasis ℂ (sectorHeightSpace Ω J) j).property
        (sectorHeightFrame Ω ⟨H,i⟩ : TensorRegister n (Fin d))
        (stdOrthonormalBasis ℂ (sectorHeightSpace Ω H) i).property

theorem sectorHeightFrame_span (Ω : TensorRegister n (Fin d)) :
    Submodule.span ℂ (Set.range (sectorHeightFrame Ω)) = ⊤ := by
  rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
  have hH (H : ℕ) : Submodule.span ℂ
      (Set.range (fun i => sectorHeightFrame Ω ⟨H,i⟩)) = sectorHeightSpace Ω H := by
    have hh := congrArg (Submodule.map (sectorHeightSpace Ω H).subtype)
      (stdOrthonormalBasis ℂ (sectorHeightSpace Ω H)).toBasis.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hh
    simpa only [← Set.range_comp, Function.comp_def, OrthonormalBasis.coe_toBasis,
      sectorHeightFrame] using hh
  simp_rw [hH]
  exact iSup_sectorHeightSpace Ω

def sectorHeightHilbertBasis
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    HilbertBasis (SectorHeightIndex Ω) ℂ (cyclicSector Ω) :=
  HilbertBasis.mk (sectorHeightFrame_orthonormal Ω mu hweight)
    (by rw [sectorHeightFrame_span]; simp)

@[simp] theorem sectorHeightHilbertBasis_apply
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (i : SectorHeightIndex Ω) :
    sectorHeightHilbertBasis Ω mu hweight i = sectorHeightFrame Ω i := by
  simp [sectorHeightHilbertBasis]

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

def sectorHeightTrace (p : Fin d → ℝ) (H : ℕ) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ (sectorHeightSpace Ω H)),
    (⟪sectorHeightFrame Ω ⟨H,i⟩,
      sectorGibbsOperator Ω mu hweight hraise p (sectorHeightFrame Ω ⟨H,i⟩)⟫_ℂ).re

theorem sectorHeightTrace_nonneg (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (H : ℕ) :
    0 ≤ sectorHeightTrace Ω mu hweight hraise p H := by
  apply Finset.sum_nonneg
  intro i _
  exact real_inner_nonneg_of_nonneg (sectorGibbsOperator_nonneg Ω mu hweight hraise p hp) _

theorem sectorPartitionFunction_eq_tsum_height (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    sectorPartitionFunction Ω mu hweight hraise p =
      ∑' H : ℕ, sectorHeightTrace Ω mu hweight hraise p H := by
  letI : Finite (SectorHeightIndex Ω) := (sectorHeightFrame_orthonormal Ω mu hweight).linearIndependent.finite
  letI : Fintype (SectorHeightIndex Ω) := Fintype.ofFinite _
  rw [sectorPartitionFunction_eq_linearMapTrace Ω mu hweight hraise p hp]
  rw [LinearMap.trace_eq_sum_inner _ (sectorHeightHilbertBasis Ω mu hweight).toOrthonormalBasis,
    Complex.re_sum]
  simp only [HilbertBasis.coe_toOrthonormalBasis, sectorHeightHilbertBasis_apply]
  rw [← tsum_fintype (L := .unconditional _)]
  simpa only [tsum_fintype, sectorHeightTrace] using
    (hasSum_fintype (fun i : SectorHeightIndex Ω =>
      (⟪sectorHeightFrame Ω i,
        sectorGibbsOperator Ω mu hweight hraise p (sectorHeightFrame Ω i)⟫_ℂ).re)).summable.tsum_sigma'
      (fun _ => (hasSum_fintype _).summable)

theorem sectorHeightTrace_summable (p : Fin d → ℝ) :
    Summable (sectorHeightTrace Ω mu hweight hraise p) := by
  letI : Finite (SectorHeightIndex Ω) := (sectorHeightFrame_orthonormal Ω mu hweight).linearIndependent.finite
  letI : Fintype (SectorHeightIndex Ω) := Fintype.ofFinite _
  have hh := (hasSum_fintype (fun i : SectorHeightIndex Ω =>
    (⟪sectorHeightFrame Ω i,
      sectorGibbsOperator Ω mu hweight hraise p (sectorHeightFrame Ω i)⟫_ℂ).re)).summable.sigma
  simpa only [tsum_fintype, sectorHeightTrace] using hh

/-- Actual height trace, bounded by the derived dimension and Boltzmann
operator bound. The estimate is uniform in the highest weight and tensor size. -/
theorem sectorHeightTrace_le (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height) (H : ℕ) :
    sectorHeightTrace Ω mu hweight hraise p H ≤
      ((H+1 : ℕ) : ℝ)^Fintype.card (PositiveRoot d) * ((∏ a, p a ^ mu a) * θ^H) := by
  have hC : 0 ≤ (∏ a, p a ^ mu a) * θ^H :=
    mul_nonneg (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a).le _)) (pow_nonneg hθ _)
  have hi (i : Fin (Module.finrank ℂ (sectorHeightSpace Ω H))) :
      (⟪sectorHeightFrame Ω ⟨H,i⟩,
        sectorGibbsOperator Ω mu hweight hraise p (sectorHeightFrame Ω ⟨H,i⟩)⟫_ℂ).re ≤
          (∏ a, p a ^ mu a) * θ^H := by
    have hn : ‖sectorHeightFrame Ω ⟨H,i⟩‖ = 1 :=
      (stdOrthonormalBasis ℂ (sectorHeightSpace Ω H)).norm_eq_one i
    have hb := tensorOperator_diagonal_norm_le_on_height Ω mu hweight p hp θ hθ hroot H
      (stdOrthonormalBasis ℂ (sectorHeightSpace Ω H) i).property
    change ‖sectorGibbsOperator Ω mu hweight hraise p (sectorHeightFrame Ω ⟨H,i⟩)‖ ≤
      ((∏ a, p a ^ mu a) * θ^H) * ‖sectorHeightFrame Ω ⟨H,i⟩‖ at hb
    rw [hn, mul_one] at hb
    exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by simpa [hn] using hb))
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℂ (sectorHeightSpace Ω H)),
        ((∏ a, p a ^ mu a) * θ^H) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Module.finrank ℂ (sectorHeightSpace Ω H) : ℝ) * ((∏ a, p a ^ mu a) * θ^H) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast sectorHeightSpace_finrank_le Ω H) hC

end Cloning.TensorLie
