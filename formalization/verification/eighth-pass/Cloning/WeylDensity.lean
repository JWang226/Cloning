import Cloning.CoherentGaussianMixture
import Cloning.CoherentKernel
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Coherent vectors are total in the actual one-mode Fock Hilbert space.
The proof uses the proved Gaussian-mixture identity: its thermal eigenvalues
are all strictly positive. No density or analyticity premise is assumed. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology

namespace Cloning.ComplexCoherent

open Cloning.InfiniteTraceClass Cloning.CoherentGaussianMixture
set_option backward.isDefEq.respectTransparency false

/-- A vector orthogonal to every coherent vector is zero. -/
theorem coherentVector_total (v : Fock)
    (h : ∀ z : ℂ, ⟪coherentVector z, v⟫_ℂ = 0) : v = 0 := by
  have hv (z : ℂ) : ⟪v, coherentVector z⟫_ℂ = 0 := inner_eq_zero_symm.mp (h z)
  have hz (n : ℕ) : ⟪v, (vectorMixture numberBasis (Thermal.geometric (1 / 2))).1
      (numberBasis n)⟫_ℂ = 0 := by
    have hi := (traceClassMatrixCoefficient v (numberBasis n)).integral_comp_comm
      (integrable_coherentProjector_gaussian (s := 1) (by norm_num))
    rw [integral_coherentProjector_gaussian_eq_thermal (by norm_num : (0 : ℝ) < 1)] at hi
    norm_num only at hi
    change traceClassMatrixCoefficient v (numberBasis n)
      (vectorMixture numberBasis (Thermal.geometric (1 / 2))) = 0
    rw [← hi]
    have he (z : ℂ) : traceClassMatrixCoefficient v (numberBasis n) (coherentProjector z) = 0 := by
      change ⟪v, (InnerProductSpace.rankOne ℂ (coherentVector z) (coherentVector z))
        (numberBasis n)⟫_ℂ = 0
      rw [InnerProductSpace.rankOne_apply, inner_smul_right, hv, mul_zero]
    simp only [he, integral_zero]
  apply numberBasis.repr.injective
  ext n
  have hn := hz n
  rw [InfiniteOccupationStates.vectorMixture_apply_basis numberBasis _
    (Thermal.geometric_hasSum (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).summable n,
    inner_smul_right] at hn
  have hp : (Thermal.geometric (1 / 2) n : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold Thermal.geometric
    positivity
  have hinner := (mul_eq_zero.mp hn).resolve_left hp
  simpa only [numberBasis.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply] using
    (inner_eq_zero_symm.mp hinner)

/-- The complex linear span of all coherent vectors is dense. -/
theorem coherentVector_dense_span :
    (Submodule.span ℂ (Set.range coherentVector)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  apply coherentVector_total
  intro z
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self z)) hv

/-- Density in the set-valued form used to extend isometries. -/
theorem dense_coherentVector_span :
    Dense (Submodule.span ℂ (Set.range coherentVector) : Set Fock) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr coherentVector_dense_span

end Cloning.ComplexCoherent
