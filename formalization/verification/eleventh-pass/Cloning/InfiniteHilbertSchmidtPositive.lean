import Cloning.InfiniteTraceClassAlgebra
import Cloning.MatrixTraceOrder

/-!
# Positive trace pairing of Hilbert–Schmidt operators

Two positive Hilbert–Schmidt operators have nonnegative trace pairing even
when neither factor is trace class. The proof uses positive finite matrix
compressions and the absolutely summable matrix expansion of their product.
The directed family of finite subsets is unrestricted, so no separability
assumption is required.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite matrix of a positive operator against any family of vectors is
positive semidefinite. No orthogonality is required. -/
theorem matrixCoefficients_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {R : H →L[ℂ] H} (hR : 0 ≤ R) (v : n → H) :
    Matrix.PosSemidef (fun i j => ⟪v i, R (v j)⟫_ℂ) := by
  have hpos := R.nonneg_iff_isPositive.mp hR
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change star ⟪v j, R (v i)⟫_ℂ = ⟪v i, R (v j)⟫_ℂ
    exact (inner_conj_symm (R (v i)) (v j)).trans
      (hpos.isSelfAdjoint.isSymmetric (v i) (v j))
  · intro z
    have h := hpos.inner_nonneg_right (∑ i, z i • v i)
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    simpa only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
      starRingEnd_apply, mul_assoc, mul_comm, mul_left_comm] using h

/-- Positivity of each finite square matrix pairing. -/
theorem finite_trace_pairing_nonneg {ι : Type*} {R S : H →L[ℂ] H}
    (hR : 0 ≤ R) (hS : 0 ≤ S) (v : ι → H) (s : Finset ι) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, ⟪v i, R (v j)⟫_ℂ * ⟪v j, S (v i)⟫_ℂ).re := by
  classical
  have h := MatrixFidelity.trace_mul_re_nonneg
    (matrixCoefficients_posSemidef hR (fun i : s => v i))
    (matrixCoefficients_posSemidef hS (fun i : s => v i))
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply] at h
  have heq : (∑ i : s, ∑ j : s, ⟪v i, R (v j)⟫_ℂ * ⟪v j, S (v i)⟫_ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, ⟪v i, R (v j)⟫_ℂ * ⟪v j, S (v i)⟫_ℂ := by
    calc
      _ = ∑ i : s, ∑ j ∈ s, ⟪v i, R (v j)⟫_ℂ * ⟪v j, S (v i)⟫_ℂ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_coe_sort s
          (fun j : ι => ⟪v i, R (v j)⟫_ℂ * ⟪v j, S (v i)⟫_ℂ)
      _ = _ := Finset.sum_coe_sort s
        (fun i : ι => ∑ j ∈ s, ⟪v i, R (v j)⟫_ℂ * ⟪v j, S (v i)⟫_ℂ)
  rw [heq] at h
  exact h

/-- Finite square subsets form a cofinal family among subsets of a Cartesian
square. This avoids selecting a countable Hilbert basis. -/
theorem tendsto_finset_square_atTop (ι : Type*) :
    Tendsto (fun s : Finset ι => s ×ˢ s) atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro s t hst
    exact Finset.product_subset_product hst hst
  · intro t
    refine ⟨t.image Prod.fst ∪ t.image Prod.snd, ?_⟩
    intro p hp
    simp only [Finset.mem_product, Finset.mem_union, Finset.mem_image]
    exact ⟨Or.inl ⟨p, hp, rfl⟩, Or.inr ⟨p, hp, rfl⟩⟩

/-- The trace pairing of two nonnegative Hilbert–Schmidt operators is
nonnegative. Neither factor is assumed to have finite trace. -/
theorem trace_re_mul_nonneg_of_isHilbertSchmidt {R S : H →L[ℂ] H}
    (hR : HilbertSchmidt.IsHilbertSchmidt R) (hS : HilbertSchmidt.IsHilbertSchmidt S)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) :
    0 ≤ (trace (R * S) (isTraceClass_mul_of_isHilbertSchmidt hR hS)).re := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let F : w × w → ℂ := fun p =>
    ⟪b p.1, R (b p.2)⟫_ℂ * ⟪b p.2, S (b p.1)⟫_ℂ
  have hF : Summable F := by
    simpa only [F, Function.uncurry, ContinuousLinearMap.adjoint_inner_left] using
      HilbertSchmidt.summable_matrix_of_hilbertSchmidt b b hR hS
  have htotal : (∑' p, F p) = trace (R * S) (isTraceClass_mul_of_isHilbertSchmidt hR hS) := by
    rw [hF.tsum_prod, trace_eq_of_hilbertBasis _ b]
    apply tsum_congr
    intro i
    simpa only [F, ContinuousLinearMap.adjoint_inner_left] using
      (HilbertSchmidt.hasSum_matrix_row_of_hilbertSchmidt (R := R) (S := S) b b i).tsum_eq
  have hlim : Tendsto (fun s : Finset w => ∑ p ∈ s ×ˢ s, F p) atTop
      (𝓝 (trace (R * S) (isTraceClass_mul_of_isHilbertSchmidt hR hS))) := by
    rw [← htotal]
    exact hF.hasSum.comp (tendsto_finset_square_atTop w)
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hre
  apply Eventually.of_forall
  intro s
  simpa only [Finset.sum_product, F] using finite_trace_pairing_nonneg hR0 hS0 b s

end Cloning.InfiniteTraceClass
