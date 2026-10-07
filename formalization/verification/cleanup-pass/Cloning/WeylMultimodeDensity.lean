import Cloning.MultimodeCoherentGaussianMixture
import Cloning.WeylDensity

/-! The literal finite-multimode coherent vectors have dense complex linear
span, including the zero-mode case. The proof uses the faithful product thermal
operator obtained by Gaussian mixing, without tensor-density hypotheses. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent

open Cloning.InfiniteTraceClass Cloning.MultimodeCoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false

/-- A finite-multimode Fock vector orthogonal to every coherent vector is zero. -/
theorem coherentVector_total {d : ℕ} (v : Fock d)
    (h : ∀ z : Fin d → ℂ, ⟪coherentVector z, v⟫_ℂ = 0) : v = 0 := by
  have hv (z : Fin d → ℂ) : ⟪v, coherentVector z⟫_ℂ = 0 := inner_eq_zero_symm.mp (h z)
  have hz (n : Fin d → ℕ) : ⟪v,
      (vectorMixture (numberBasis d) (fun k ↦ ∏ i, Thermal.geometric (1 / 2) (k i))).1
        (numberBasis d n)⟫_ℂ = 0 := by
    have hi := (traceClassMatrixCoefficient v (numberBasis d n)).integral_comp_comm
      (integrable_coherentProjector_gaussian (s := fun _ : Fin d ↦ 1)
        (fun _ ↦ by norm_num))
    rw [integral_coherentProjector_gaussian_eq_productThermal
      (s := fun _ : Fin d ↦ 1) (fun _ ↦ by norm_num)] at hi
    norm_num only at hi
    change traceClassMatrixCoefficient v (numberBasis d n)
      (vectorMixture (numberBasis d) (fun k ↦ ∏ i, Thermal.geometric (1 / 2) (k i))) = 0
    rw [← hi]
    have he (z : Fin d → ℂ) :
        traceClassMatrixCoefficient v (numberBasis d n) (coherentProjector z) = 0 := by
      change ⟪v, (InnerProductSpace.rankOne ℂ (coherentVector z) (coherentVector z))
        (numberBasis d n)⟫_ℂ = 0
      rw [InnerProductSpace.rankOne_apply, inner_smul_right, hv, mul_zero]
    simp only [he, integral_zero]
  apply (numberBasis d).repr.injective
  ext n
  have hn := hz n
  rw [InfiniteOccupationStates.vectorMixture_apply_basis (numberBasis d) _
    (Thermal.multimode_geometric_hasSum
      (q := fun _ : Fin d ↦ 1 / 2) (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)).summable n,
    inner_smul_right] at hn
  have hp : ((∏ i : Fin d, Thermal.geometric (1 / 2) (n i) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Finset.prod_pos
    intro i _
    unfold Thermal.geometric
    positivity
  have hinner := (mul_eq_zero.mp hn).resolve_left hp
  simpa only [(numberBasis d).repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply] using
    (inner_eq_zero_symm.mp hinner)

/-- Multimode coherent vectors span a dense complex subspace. -/
theorem coherentVector_dense_span (d : ℕ) :
    (Submodule.span ℂ (Set.range (fun z : Fin d → ℂ ↦ coherentVector z))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  apply coherentVector_total
  intro z
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self z)) hv

/-- Set-valued density of the finite-multimode coherent span. -/
theorem dense_coherentVector_span (d : ℕ) :
    Dense (Submodule.span ℂ (Set.range (fun z : Fin d → ℂ ↦ coherentVector z)) : Set (Fock d)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentVector_dense_span d)

end Cloning.MultimodeCoherent
