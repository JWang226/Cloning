import Cloning.InfiniteTraceClassCutoffConvergence
import Cloning.InfiniteFidelityContinuity
import Cloning.MatrixFidelityBlockBound
import Cloning.InfiniteFiniteCorner

/-!
# Trace-class block bounds for root fidelity

Finite-basis compressions reduce the block trace inequality to the matrix
theorem. All limits below are in the actual analytic trace norm.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compressing a positive two-by-two operator quadratic form yields an
actual positive finite block matrix. -/
theorem finite_block_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → H) (A B X : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1)
    (hblock : ∀ x y : H, 0 ≤ ⟪x, A.1 x⟫_ℂ + ⟪x, X.1 y⟫_ℂ +
      ⟪y, (star X.1) x⟫_ℂ + ⟪y, B.1 y⟫_ℂ) :
    (Matrix.fromBlocks
      (fun i j => ⟪v i, A.1 (v j)⟫_ℂ)
      (fun i j => ⟪v i, X.1 (v j)⟫_ℂ)
      (Matrix.conjTranspose (fun i j => ⟪v i, X.1 (v j)⟫_ℂ))
      (fun i j => ⟪v i, B.1 (v j)⟫_ℂ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (matrixCoefficients_posSemidef hA v).isHermitian.fromBlocks rfl
      (matrixCoefficients_posSemidef hB v).isHermitian
  · intro z
    have h := hblock (∑ i, z (Sum.inl i) • v i) (∑ i, z (Sum.inr i) • v i)
    have hstar (i j : ι) : ⟪v i, (star X.1) (v j)⟫_ℂ = star ⟪v j, X.1 (v i)⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      exact (inner_conj_symm _ _).symm
    have hform (T : H →L[ℂ] H) (c d : ι → ℂ) :
        ⟪∑ i, c i • v i, T (∑ j, d j • v j)⟫_ℂ =
          ∑ i, ∑ j, star (c i) * ⟪v i, T (v j)⟫_ℂ * d j := by
      simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right, Finset.mul_sum, starRingEnd_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [hform, hstar] at h
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_add_distrib,
      mul_add, add_assoc]
    simp only [mul_assoc, add_assoc] at h
    convert h using 1
    abel

theorem sandwich_tendsto_of_strong_projections_selfAdjoint {α : Type*} {l : Filter α}
    (P : α → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hstrong : ∀ x : H, Tendsto (fun a => P a x) l (𝓝 x))
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    Tendsto (fun a => sandwichCLM (P a) (P a) A) l (𝓝 A) := by
  have hp := sandwich_tendsto_of_strong_projections P hP hstrong
    (TraceClass.positivePart A hA) (TraceClass.positivePart_nonneg A hA)
  have hn := sandwich_tendsto_of_strong_projections P hP hstrong
    (TraceClass.negativePart A hA) (TraceClass.negativePart_nonneg A hA)
  simpa only [← map_sub, TraceClass.positivePart_sub_negativePart] using hp.sub hn

/-- Compression converges for arbitrary trace-class inputs, including the
off-diagonal entries of a positive operator block. -/
theorem sandwich_tendsto_of_strong_projections_all {α : Type*} {l : Filter α}
    (P : α → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hstrong : ∀ x : H, Tendsto (fun a => P a x) l (𝓝 x))
    (A : TraceClass H) :
    Tendsto (fun a => sandwichCLM (P a) (P a) A) l (𝓝 A) := by
  have hr := sandwich_tendsto_of_strong_projections_selfAdjoint P hP hstrong
    (TraceClass.realComponent A) (TraceClass.realComponent_isSelfAdjoint A)
  have hi := sandwich_tendsto_of_strong_projections_selfAdjoint P hP hstrong
    (TraceClass.imaginaryComponent A) (TraceClass.imaginaryComponent_isSelfAdjoint A)
  simpa only [← map_smul, ← map_add,
    TraceClass.realComponent_add_I_smul_imaginaryComponent] using hr.add (hi.const_smul Complex.I)

theorem basis_sandwich_tendsto {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A : TraceClass H) :
    Tendsto (fun s : Finset ι => sandwichCLM (basisProjection b s) (basisProjection b s) A)
      atTop (𝓝 A) :=
  sandwich_tendsto_of_strong_projections_all _ (basisProjection_isStarProjection b)
    (basisProjection_tendsto b) A

end
end Cloning.InfiniteTraceClass

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter InfiniteTraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Joint continuity in the trace-class topology follows from the proved
dimension-independent trace-distance modulus. -/
theorem tendsto_fidelity_traceClass {α : Type*} {l : Filter α}
    (A B : α → TraceClass H) (C D : TraceClass H)
    (hA : ∀ a, 0 ≤ (A a).1) (hB : ∀ a, 0 ≤ (B a).1)
    (hC : 0 ≤ C.1) (hD : 0 ≤ D.1)
    (hAC : Tendsto A l (𝓝 C)) (hBD : Tendsto B l (𝓝 D)) :
    Tendsto (fun a => fidelity (A a).1 (B a).1 (hA a) (hB a) (A a).2 (B a).2) l
      (𝓝 (fidelity C.1 D.1 hC hD C.2 D.2)) := by
  have hAnorm : Tendsto (fun a => ‖A a - C‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hAC
  have hBnorm : Tendsto (fun a => ‖B a - D‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hBD
  have hBtrace : Tendsto (fun a => (trace (B a).1 (B a).2).re) l
      (𝓝 (trace D.1 D.2).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (traceCLM.continuous.tendsto D |>.comp hBD)
  have hbound : Tendsto (fun a => Real.sqrt ‖A a - C‖ *
      Real.sqrt (trace (B a).1 (B a).2).re +
      Real.sqrt ‖B a - D‖ * Real.sqrt (trace C.1 C.2).re) l (𝓝 0) := by
    simpa using (hAnorm.sqrt.mul hBtrace.sqrt).add (hBnorm.sqrt.mul_const _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hbound
  intro a
  simpa only [Real.norm_eq_abs] using fidelity_continuity
    (hA a) (hB a) hC hD (A a).2 (B a).2 C.2 D.2

/-- The real trace of an off-diagonal entry of a positive trace-class block
is at most the actual root fidelity of its diagonal entries. Finite corners
are proved positive and the matrix bound is passed to the trace-norm limit. -/
theorem trace_re_le_fidelity_of_block (A B X : TraceClass H)
    (hA : 0 ≤ A.1) (hB : 0 ≤ B.1)
    (hblock : ∀ x y : H, 0 ≤ ⟪x, A.1 x⟫_ℂ + ⟪x, X.1 y⟫_ℂ +
      ⟪y, (star X.1) x⟫_ℂ + ⟪y, B.1 y⟫_ℂ) :
    (traceCLM X).re ≤ fidelity A.1 B.1 hA hB A.2 B.2 := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let P := fun s : Finset w => basisProjection b s
  let compress := fun (s : Finset w) (T : TraceClass H) => sandwichCLM (P s) (P s) T
  have hpos (s : Finset w) (T : TraceClass H) (hT : 0 ≤ T.1) :
      0 ≤ (compress s T).1 :=
    sandwichCLM_nonneg (basisProjection_isStarProjection b s).isSelfAdjoint T hT
  have htrace : Tendsto (fun s : Finset w => (traceCLM (compress s X)).re) atTop
      (𝓝 (traceCLM X).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (traceCLM.continuous.tendsto X |>.comp (basis_sandwich_tendsto b X))
  have hfid := tendsto_fidelity_traceClass (fun s => compress s A) (fun s => compress s B)
    A B (fun s => hpos s A hA) (fun s => hpos s B hB) hA hB
    (basis_sandwich_tendsto b A) (basis_sandwich_tendsto b B)
  apply le_of_tendsto_of_tendsto htrace hfid
  apply Eventually.of_forall
  intro s
  let v : s → H := fun i => b i
  have hv : Orthonormal ℂ v := InfiniteFiniteCorner.basisFamily_orthonormal b s
  have hMA := InfiniteFiniteCorner.matrixOf_posSemidef v hA
  have hMB := InfiniteFiniteCorner.matrixOf_posSemidef v hB
  have hfinite := MatrixFidelity.trace_re_le_fidelity_of_block_posSemidef
    (finite_block_posSemidef v A B X hA hB hblock)
  have eX : traceCLM (compress s X) =
      Matrix.trace (InfiniteFiniteCorner.matrixOf v X.1) := by
    simpa only [v, compress, P, InfiniteFiniteCorner.ofMatrix_matrixOf_basis, traceCLM_apply,
      sandwichCLM_coe] using InfiniteFiniteCorner.trace_ofMatrix hv
        (InfiniteFiniteCorner.matrixOf v X.1)
  have eF : fidelity (compress s A).1 (compress s B).1 (hpos s A hA) (hpos s B hB)
      (compress s A).2 (compress s B).2 =
      MatrixFidelity.fidelity (InfiniteFiniteCorner.matrixOf v A.1)
        (InfiniteFiniteCorner.matrixOf v B.1) := by
    simpa only [v, compress, P, InfiniteFiniteCorner.ofMatrix_matrixOf_basis, sandwichCLM_coe] using
      InfiniteFiniteCorner.fidelity_ofMatrix hv hMA hMB
  change (traceCLM (compress s X)).re ≤ fidelity (compress s A).1 (compress s B).1
    (hpos s A hA) (hpos s B hB) (compress s A).2 (compress s B).2
  rw [eX, eF]
  exact hfinite

end
end Cloning.InfiniteFidelity
