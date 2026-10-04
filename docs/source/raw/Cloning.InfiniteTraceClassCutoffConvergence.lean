import Cloning.InfiniteTraceClassCutoff
import Cloning.InfiniteTraceClassDecomposition
import Cloning.InfinitePureStateContinuity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Genuine trace-norm convergence of finite-basis projection cutoffs.
The proof uses the proved rank-one expansion of positive trace-class operators,
not an assumed finite-rank density or truncation estimate. -/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Orthogonal projection onto a finite set of actual Hilbert-basis vectors. -/
def basisProjection {ι : Type*} (b : HilbertBasis ι ℂ H) (s : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (b i) (b i)

omit [CompleteSpace H] in
lemma basisProjection_apply {ι : Type*} (b : HilbertBasis ι ℂ H) (s : Finset ι) (x : H) :
    basisProjection b s x = ∑ i ∈ s, b.repr x i • b i := by
  simp [basisProjection, ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply,
    HilbertBasis.repr_apply_apply]

lemma basisProjection_isStarProjection {ι : Type*} (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    IsStarProjection (basisProjection b s) := by
  classical
  constructor
  · change basisProjection b s * basisProjection b s = basisProjection b s
    ext x
    simp only [ContinuousLinearMap.mul_apply, basisProjection_apply]
    simp [map_sum, map_smul, HilbertBasis.repr_apply_apply,
      orthonormal_iff_ite.mp b.orthonormal]
  · change star (basisProjection b s) = basisProjection b s
    simp [basisProjection, ContinuousLinearMap.star_eq_adjoint]

omit [CompleteSpace H] in
lemma basisProjection_tendsto {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    Tendsto (fun s : Finset ι => basisProjection b s x) atTop (𝓝 x) := by
  simpa only [basisProjection_apply] using b.hasSum_repr x

omit [CompleteSpace H] in
lemma basisProjection_mem_span {ι : Type*} (b : HilbertBasis ι ℂ H)
    (s : Finset ι) (x : H) :
    basisProjection b s x ∈ Submodule.span ℂ (b '' (s : Set ι)) := by
  rw [basisProjection_apply]
  exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, hi, rfl⟩))

lemma sandwichCLM_vectorProjector (P : H →L[ℂ] H) (hP : IsSelfAdjoint P) (x : H) :
    sandwichCLM P P (vectorProjector x) = vectorProjector (P x) := by
  apply Subtype.ext
  change P * InnerProductSpace.rankOne ℂ x x * P = InnerProductSpace.rankOne ℂ (P x) (P x)
  simp only [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
    InnerProductSpace.rankOne_comp]
  rw [← ContinuousLinearMap.star_eq_adjoint, hP.star_eq]

lemma norm_sandwich_projection_le {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) : ‖sandwichCLM P P A‖ ≤ ‖A‖ := by
  change traceNorm (P * A.1 * P) _ ≤ traceNorm A.1 A.2
  calc
    traceNorm (P * A.1 * P) _ ≤ ‖P‖ * traceNorm A.1 A.2 * ‖P‖ :=
      traceNorm_mul_mul_le A.2 _
    _ ≤ 1 * traceNorm A.1 A.2 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hP.norm_le (traceNorm_nonneg _ _))
        hP.norm_le (norm_nonneg _) (mul_nonneg zero_le_one (traceNorm_nonneg _ _))
    _ = traceNorm A.1 A.2 := by ring

/-- Strong convergence of orthogonal projections gives trace-norm convergence
of their compressions on every positive trace-class input. -/
theorem sandwich_tendsto_of_strong_projections {α : Type*} {l : Filter α}
    (P : α → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hstrong : ∀ x : H, Tendsto (fun a => P a x) l (𝓝 x))
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    Tendsto (fun a => sandwichCLM (P a) (P a) A) l (𝓝 A) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let v : w → H := fun i => CFC.sqrt A.1 (b i)
  have hseries : HasSum (fun i => vectorProjector (v i)) A :=
    positive_rankOne_series hA A.2 b
  have hmass : Summable (fun i => ‖vectorProjector (v i)‖) :=
    (positive_rankOne_mass hA A.2 b).summable
  have hconv : Tendsto (fun a => ∑' i, sandwichCLM (P a) (P a) (vectorProjector (v i))) l
      (𝓝 (∑' i, vectorProjector (v i))) := by
    apply tendsto_tsum_of_dominated_convergence hmass
    · intro i
      simp only [sandwichCLM_vectorProjector _ (hP _).isSelfAdjoint]
      exact vectorProjector_tendsto (hstrong (v i))
    · exact Eventually.of_forall (fun a i => norm_sandwich_projection_le (hP a) _)
  have hsum (a : α) :
      (∑' i, sandwichCLM (P a) (P a) (vectorProjector (v i))) = sandwichCLM (P a) (P a) A :=
    (hseries.mapL (sandwichCLM (P a) (P a))).tsum_eq
  simpa only [hsum, hseries.tsum_eq] using hconv

/-- Compression and replacement converge in the actual trace norm, with no
tail or finite-rank approximation premise. -/
theorem projectionReplacement_tendsto_of_strong_projections {α : Type*} {l : Filter α}
    (P : α → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hstrong : ∀ x : H, Tendsto (fun a => P a x) l (𝓝 x))
    (σ : DensityState H) (A : TraceClass H) (hA : 0 ≤ A.1) :
    Tendsto (fun a => projectionReplacement (P a) (hP a) σ A) l (𝓝 A) := by
  have hc := sandwich_tendsto_of_strong_projections P hP hstrong A hA
  have ht : Tendsto (fun a => traceCLM A - traceCLM (sandwichCLM (P a) (P a) A)) l
      (𝓝 (0 : ℂ)) := by
    have htr := traceCLM.continuous.tendsto A |>.comp hc
    simpa using htr.const_sub (traceCLM A)
  have heq (a : α) : traceCLM (sandwichCLM (1 - P a) (1 - P a) A) =
      traceCLM A - traceCLM (sandwichCLM (P a) (P a) A) := by
    linear_combination traceCLM_projection_split (hP a) A
  have hresult := hc.add (ht.smul_const (TraceClass.ofOperator σ.op σ.traceClass))
  simpa only [zero_smul, add_zero, projectionReplacement_apply, heq] using hresult

/-- The explicitly defined finite-basis cutoffs converge on every density operator. -/
theorem basisProjectionReplacement_tendsto {ι : Type*} (b : HilbertBasis ι ℂ H)
    (σ : DensityState H) (A : TraceClass H) (hA : 0 ≤ A.1) :
    Tendsto (fun s : Finset ι =>
      projectionReplacement (basisProjection b s) (basisProjection_isStarProjection b s) σ A)
      atTop (𝓝 A) :=
  projectionReplacement_tendsto_of_strong_projections _ (basisProjection_isStarProjection b)
    (basisProjection_tendsto b) σ A hA

/-- Contractivity turns pointwise approximation into uniform approximation on
any trace-norm compact family of positive operators. -/
theorem PositiveTracePreservingMap.tendstoUniformlyOn_of_isCompact
    {α : Type*} {l : Filter α} (Φ : α → PositiveTracePreservingMap H H)
    {S : Set (TraceClass H)} (hS : IsCompact S) (hpos : ∀ A ∈ S, 0 ≤ A.1)
    (hpoint : ∀ A ∈ S, Tendsto (fun a => Φ a A) l (𝓝 A)) :
    TendstoUniformlyOn (fun a A => Φ a A) (fun A => A) l S := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htS, ht, hcover⟩ := hS.finite_cover_balls (show 0 < ε / 3 by positivity)
  have hevent : ∀ᶠ a in l, ∀ B ∈ t, dist (Φ a B) B < ε / 3 := by
    rw [ht.eventually_all]
    intro B hB
    exact (Metric.tendsto_nhds.mp (hpoint B (htS hB))) (ε / 3) (by positivity)
  filter_upwards [hevent] with a ha
  intro A hA
  obtain ⟨B, hB, hAB⟩ : ∃ B ∈ t, dist A B < ε / 3 := by
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcover hA
  have hcon : dist (Φ a B) (Φ a A) ≤ dist B A := by
    simpa only [dist_eq_norm] using (Φ a).norm_map_sub_le B A
      (hpos B (htS hB)) (hpos A hA)
  have hnet := ha B hB
  have htri := dist_triangle A B (Φ a A)
  have htri' := dist_triangle B (Φ a B) (Φ a A)
  rw [dist_comm B A] at hcon
  rw [dist_comm (Φ a B) B] at hnet
  linarith

/-- Uniform cutoff approximation on compact positive trace-class families is a
theorem, rather than a uniform tail hypothesis. -/
theorem basisProjectionReplacement_tendstoUniformlyOn {ι : Type*}
    (b : HilbertBasis ι ℂ H) (σ : DensityState H) {S : Set (TraceClass H)}
    (hS : IsCompact S) (hpos : ∀ A ∈ S, 0 ≤ A.1) :
    TendstoUniformlyOn (fun s : Finset ι =>
      projectionReplacement (basisProjection b s) (basisProjection_isStarProjection b s) σ)
      (fun A => A) atTop S := by
  exact PositiveTracePreservingMap.tendstoUniformlyOn_of_isCompact _ hS hpos
    (fun A hA => basisProjectionReplacement_tendsto b σ A (hpos A hA))

omit [CompleteSpace H] in
/-- A designated basis vector is fixed whenever it belongs to the cutoff. -/
lemma basisProjection_apply_basis_of_mem {ι : Type*} (b : HilbertBasis ι ℂ H)
    (s : Finset ι) {i : ι} (hi : i ∈ s) : basisProjection b s (b i) = b i := by
  classical
  simp [basisProjection_apply, HilbertBasis.repr_apply_apply,
    orthonormal_iff_ite.mp b.orthonormal, hi]

/-- A finite cutoff with a pure replacement vector included in its retained subspace. -/
def finiteBasisCutoff {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (i₀ : ι) (s : Finset ι) : PositiveTracePreservingMap H H :=
  projectionReplacement (basisProjection b (insert i₀ s))
    (basisProjection_isStarProjection b (insert i₀ s))
    (DensityState.pure (b i₀) (b.orthonormal.norm_eq_one i₀))

/-- Every output of the finite cutoff is supported on the explicit finite basis span. -/
lemma finiteBasisCutoff_supported {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (i₀ : ι) (s : Finset ι) (A : TraceClass H) :
    basisProjection b (insert i₀ s) * (finiteBasisCutoff b i₀ s A).1 *
        basisProjection b (insert i₀ s) = (finiteBasisCutoff b i₀ s A).1 := by
  apply projectionReplacement_supported
  have h := sandwichCLM_vectorProjector (basisProjection b (insert i₀ s))
    (basisProjection_isStarProjection b (insert i₀ s)).isSelfAdjoint (b i₀)
  rw [basisProjection_apply_basis_of_mem b _ (Finset.mem_insert_self _ _)] at h
  exact congrArg Subtype.val h

lemma finiteBasisCutoff_mem_span {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (i₀ : ι) (s : Finset ι) (A : TraceClass H) (x : H) :
    (finiteBasisCutoff b i₀ s A).1 x ∈
      Submodule.span ℂ (b '' ((insert i₀ s : Finset ι) : Set ι)) := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) (finiteBasisCutoff_supported b i₀ s A)
  change basisProjection b (insert i₀ s)
    ((finiteBasisCutoff b i₀ s A).1 (basisProjection b (insert i₀ s) x)) =
      (finiteBasisCutoff b i₀ s A).1 x at h
  rw [← h]
  exact basisProjection_mem_span b _ _

/-- Every output operator has finite-dimensional range, with no finite-dimensional
assumption on the ambient Hilbert space. -/
theorem finiteBasisCutoff_finiteDimensional_range {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (i₀ : ι) (s : Finset ι) (A : TraceClass H) :
    FiniteDimensional ℂ (LinearMap.range (finiteBasisCutoff b i₀ s A).1.toLinearMap) := by
  let U := Submodule.span ℂ (b '' ((insert i₀ s : Finset ι) : Set ι))
  letI instFiniteDimensionalCutoffSpan : FiniteDimensional ℂ U :=
    FiniteDimensional.span_of_finite ℂ ((insert i₀ s).finite_toSet.image b)
  apply Submodule.finiteDimensional_of_le (S₂ := U)
  rintro _ ⟨x, rfl⟩
  exact finiteBasisCutoff_mem_span b i₀ s A x

theorem finiteBasisCutoff_tendsto {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (i₀ : ι) (A : TraceClass H) (hA : 0 ≤ A.1) :
    Tendsto (fun s : Finset ι => finiteBasisCutoff b i₀ s A) atTop (𝓝 A) := by
  have hi : Tendsto (fun s : Finset ι => insert i₀ s) atTop atTop :=
    tendsto_atTop_mono (fun s => Finset.subset_insert i₀ s) tendsto_id
  exact (basisProjectionReplacement_tendsto b
    (DensityState.pure (b i₀) (b.orthonormal.norm_eq_one i₀)) A hA).comp hi

theorem finiteBasisCutoff_tendstoUniformlyOn {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ H) (i₀ : ι) {S : Set (TraceClass H)}
    (hS : IsCompact S) (hpos : ∀ A ∈ S, 0 ≤ A.1) :
    TendstoUniformlyOn (fun s : Finset ι => finiteBasisCutoff b i₀ s)
      (fun A => A) atTop S :=
  PositiveTracePreservingMap.tendstoUniformlyOn_of_isCompact _ hS hpos
    (fun A hA => finiteBasisCutoff_tendsto b i₀ A (hpos A hA))

end
end Cloning.InfiniteTraceClass
