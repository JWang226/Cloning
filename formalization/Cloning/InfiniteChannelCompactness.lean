import Cloning.InfiniteTraceClassFamilyCompactness
import Cloning.InfiniteTraceClassSeparable
import Cloning.InfiniteTraceClassPairing
import Cloning.InfiniteBilinearWeakClosure

/-! Actual subsequence extraction of a completely positive trace-nonincreasing
map from any sequence of quantum channels between separable Hilbert spaces.
There is no assumed convergent map or subsequence in the hypotheses. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology ComplexOrder InnerProductSpace
open Filter TopologicalSpace

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [SeparableSpace K]

/-- The subsequence and the raw operator-valued limit are constructed from
Banach--Alaoglu and separability of the trace-class input space. -/
theorem exists_subsequence_bounded_operator_limit
    (L : ℕ → TraceClass H →L[ℂ] TraceClass K) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n A, ‖L n A‖ ≤ C * ‖A‖) :
    ∃ T : TraceClass H → K →L[ℂ] K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ A x y,
      Tendsto (fun n => ⟪x, (L (φ n) A).1 y⟫_ℂ) atTop
        (𝓝 ⟪x, T A y⟫_ℂ) := by
  let U : ℕ → TraceClass H →L[ℂ] ((K →L[ℂ] K) →L[ℂ] ℂ) := fun n =>
    tracePairingCLM.comp (L n)
  have hU (n : ℕ) (A : TraceClass H) : ‖U n A‖ ≤ C * ‖A‖ :=
    (norm_tracePairing_le _).trans (hbound n A)
  let O : ℕ × (ℕ × ℕ) → TraceClass H × (K →L[ℂ] K) := fun i =>
    (denseSeq (TraceClass H) i.1,
      InnerProductSpace.rankOne ℂ (denseSeq K i.2.1) (denseSeq K i.2.2))
  obtain ⟨f, hf, hclosure, φ, hφ, hlim⟩ :=
    exists_subsequence_family_functionals (fun n A => U n A)
      (fun A => C * ‖A‖) hU O
  -- The weak product limit retains the linearity of every member of the sequence.
  -- The helper below bundles this actual closure consequence, with the inherited bound.
  let G : TraceClass H →L[ℂ] ((K →L[ℂ] K) →L[ℂ] ℂ) :=
    Cloning.InfiniteBilinearWeakClosure.boundedStrongClosureMap U f hclosure C hf
  have hG (A : TraceClass H) : G A = f A := rfl
  have hdense (i : ℕ) (x y : K) :
      Tendsto (fun n => U (φ n) (denseSeq (TraceClass H) i)
        (InnerProductSpace.rankOne ℂ x y)) atTop
        (𝓝 (G (denseSeq (TraceClass H) i) (InnerProductSpace.rankOne ℂ x y))) := by
    rw [hG]
    exact tendsto_rankOne_of_dense_evaluations
      (fun n => U (φ n) (denseSeq (TraceClass H) i)) (f (denseSeq (TraceClass H) i))
      (C * ‖denseSeq (TraceClass H) i‖) (by positivity)
      (fun n => hU (φ n) _) (hf _) (fun j => hlim (i, j)) x y
  have hall (A : TraceClass H) (x y : K) :
      Tendsto (fun n => U (φ n) A (InnerProductSpace.rankOne ℂ x y)) atTop
        (𝓝 (G A (InnerProductSpace.rankOne ℂ x y))) := by
    let R := InnerProductSpace.rankOne ℂ x y
    let un : ℕ → TraceClass H →L[ℂ] ℂ := fun n =>
      (ContinuousLinearMap.apply ℂ ℂ R).comp (U (φ n))
    let g : TraceClass H →L[ℂ] ℂ := (ContinuousLinearMap.apply ℂ ℂ R).comp G
    have hun (n : ℕ) : ‖un n‖ ≤ C * ‖R‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro B
      change ‖U (φ n) B R‖ ≤ _
      calc
        _ ≤ ‖U (φ n) B‖ * ‖R‖ := (U (φ n) B).le_opNorm R
        _ ≤ (C * ‖B‖) * ‖R‖ := mul_le_mul_of_nonneg_right (hU (φ n) B) (norm_nonneg R)
        _ = _ := by ring
    have hg : ‖g‖ ≤ C * ‖R‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro B
      change ‖G B R‖ ≤ _
      rw [hG]
      calc
        _ ≤ ‖f B‖ * ‖R‖ := (f B).le_opNorm R
        _ ≤ (C * ‖B‖) * ‖R‖ := mul_le_mul_of_nonneg_right (hf B) (norm_nonneg R)
        _ = _ := by ring
    exact tendsto_functionals_at_closure un g (C * ‖R‖) (by positivity) hun hg
      (S := Set.range (denseSeq (TraceClass H)))
      (by rintro _ ⟨i, rfl⟩; exact hdense i x y)
      (denseRange_denseSeq (TraceClass H) A)
  refine ⟨fun A => normalPartOp (G A), φ, hφ, ?_⟩
  intro A x y
  have h := hall A y x
  simpa only [U, ContinuousLinearMap.comp_apply, tracePairingCLM_apply,
    tracePairing_rankOne, normalPart_inner] using h

end
end Cloning.InfiniteTraceClass
