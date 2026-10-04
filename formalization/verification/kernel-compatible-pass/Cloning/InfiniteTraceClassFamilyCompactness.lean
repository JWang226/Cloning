import Cloning.InfiniteTraceClassCompactness

/-! Simultaneous subsequence extraction by Tychonoff compactness followed by
countably many evaluations. The chosen family lies in the closure of the
original sequence, preserving closed algebraic constraints. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology ComplexOrder InnerProductSpace
open Filter TopologicalSpace

/-- Actual simultaneous extraction from a bounded family of dual spaces.
The index `I` may be uncountable; only the observations must be countable. -/
theorem exists_subsequence_family_functionals {I J E : Type*} [Countable J]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℕ → I → E →L[ℂ] ℂ) (C : I → ℝ)
    (hu : ∀ n i, ‖u n i‖ ≤ C i) (O : J → I × E) :
    ∃ f : I → E →L[ℂ] ℂ,
      (∀ i, ‖f i‖ ≤ C i) ∧
      (fun i => StrongDual.toWeakDual (f i)) ∈
        closure (Set.range (fun n i => StrongDual.toWeakDual (u n i))) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
        Tendsto (fun n => u (φ n) (O j).1 (O j).2) atTop
          (𝓝 (f (O j).1 (O j).2)) := by
  let v : ℕ → I → WeakDual ℂ E := fun n i => StrongDual.toWeakDual (u n i)
  let B : Set (I → WeakDual ℂ E) := Set.pi Set.univ
    (fun i => WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (C i))
  have hB : IsCompact B := isCompact_univ_pi
    (fun i => WeakDual.isCompact_closedBall ℂ (0 : E →L[ℂ] ℂ) (C i))
  have hvB : Set.range v ⊆ B := by
    rintro _ ⟨n, rfl⟩ i _
    simpa [v, Metric.mem_closedBall, dist_zero_right] using hu n i
  have hcsub : closure (Set.range v) ⊆ B := closure_minimal hvB hB.isClosed
  have hc : IsCompact (closure (Set.range v)) := hB.of_isClosed_subset isClosed_closure hcsub
  let ev : (I → WeakDual ℂ E) → J → ℂ := fun f j => f (O j).1 (O j).2
  have hev : Continuous ev := continuous_pi (fun j =>
    (WeakDual.eval_continuous (O j).2).comp (continuous_apply (O j).1))
  have hmem (n : ℕ) : ev (v n) ∈ ev '' closure (Set.range v) :=
    ⟨v n, subset_closure (Set.mem_range_self n), rfl⟩
  obtain ⟨g, hg, φ, hφ, hlim⟩ := (hc.image hev).tendsto_subseq hmem
  obtain ⟨f, hf, rfl⟩ := hg
  refine ⟨fun i => WeakDual.toStrongDual (f i), ?_, hf, φ, hφ, ?_⟩
  · intro i
    have hi := hcsub hf i (Set.mem_univ i)
    simpa [Metric.mem_closedBall, dist_zero_right] using hi
  · intro j
    exact (continuous_apply j).tendsto _ |>.comp hlim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma rankOne_mem_closure_denseSeq [SeparableSpace H] (x y : H) :
    InnerProductSpace.rankOne ℂ x y ∈ closure
      (Set.range (fun i : ℕ × ℕ => InnerProductSpace.rankOne ℂ
        (denseSeq H i.1) (denseSeq H i.2))) := by
  have hd : DenseRange (fun i : ℕ × ℕ => (denseSeq H i.1, denseSeq H i.2)) :=
    (denseRange_denseSeq H).prodMap (denseRange_denseSeq H)
  have hr : Continuous (fun p : H × H => InnerProductSpace.rankOne ℂ p.1 p.2) :=
    (ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp
      (((innerSL ℂ).continuous.comp continuous_snd).prodMk continuous_fst)
  have h := hr.range_subset_closure_image_dense hd ⟨(x, y), rfl⟩
  simpa only [← Set.range_comp, Function.comp_def] using h

lemma tendsto_rankOne_of_dense_evaluations [SeparableSpace H]
    (u : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ) (f : (H →L[ℂ] H) →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hf : ‖f‖ ≤ C)
    (hlim : ∀ i : ℕ × ℕ, Tendsto (fun n => u n
      (InnerProductSpace.rankOne ℂ (denseSeq H i.1) (denseSeq H i.2))) atTop
      (𝓝 (f (InnerProductSpace.rankOne ℂ (denseSeq H i.1) (denseSeq H i.2)))))
    (x y : H) : Tendsto (fun n => u n (InnerProductSpace.rankOne ℂ x y)) atTop
      (𝓝 (f (InnerProductSpace.rankOne ℂ x y))) := by
  apply tendsto_functionals_at_closure u f C hC hu hf
    (S := Set.range (fun i : ℕ × ℕ => InnerProductSpace.rankOne ℂ
      (denseSeq H i.1) (denseSeq H i.2)))
  · rintro _ ⟨i, rfl⟩
    exact hlim i
  · exact rankOne_mem_closure_denseSeq x y

/-- One subsequence works simultaneously for every member of a countable
family of positive trace-bounded operator sequences. -/
theorem exists_subsequence_weak_operator_limits {J : Type*} [Countable J]
    [SeparableSpace H] (A : ℕ → J → TraceClass H)
    (hA : ∀ n j, 0 ≤ (A n j).1) (C : J → ℝ)
    (htrace : ∀ n j, (trace (A n j).1 (A n j).2).re ≤ C j) :
    ∃ T : J → TraceClass H,
      (∀ j, 0 ≤ (T j).1 ∧ (trace (T j).1 (T j).2).re ≤ C j) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j x y,
        Tendsto (fun n => ⟪y, (A (φ n) j).1 x⟫_ℂ) atTop (𝓝 ⟪y, (T j).1 x⟫_ℂ) := by
  let u := fun n j => tracePairing (A n j)
  have hnorm (n : ℕ) (j : J) : ‖A n j‖ ≤ C j := by
    rw [TraceClass.norm_eq_trace_re_of_nonneg _ (hA n j)]
    exact htrace n j
  have hu (n : ℕ) (j : J) : ‖u n j‖ ≤ C j :=
    (norm_tracePairing_le _).trans (hnorm n j)
  let O : J × (ℕ × ℕ) → J × (H →L[ℂ] H) := fun j =>
    (j.1, InnerProductSpace.rankOne ℂ (denseSeq H j.2.1) (denseSeq H j.2.2))
  obtain ⟨f, hf, _, φ, hφ, hlim⟩ := exists_subsequence_family_functionals u C hu O
  have hcoeff (j : J) (x y : H) :
      Tendsto (fun n => ⟪y, (A (φ n) j).1 x⟫_ℂ) atTop
        (𝓝 ⟪y, normalPartOp (f j) x⟫_ℂ) := by
    have h := tendsto_rankOne_of_dense_evaluations (fun n => u (φ n) j) (f j) (C j)
      ((norm_nonneg (A 0 j)).trans (hnorm 0 j))
      (fun n => hu (φ n) j) (hf j) (fun i => hlim (j, i)) x y
    simpa only [u, tracePairing_rankOne, normalPart_inner] using h
  have hex (j : J) : 0 ≤ normalPartOp (f j) ∧
      ∃ ht : IsTraceClass (normalPartOp (f j)),
        (trace (normalPartOp (f j)) ht).re ≤ C j := by
    apply InfiniteTraceClassWeakLimit.traceClass_of_diagonal_tendsto (l := atTop)
      (fun n => (A (φ n) j).1) (normalPartOp (f j)) (fun n => hA (φ n) j)
      (fun n => (A (φ n) j).2) (C j) (fun n => htrace (φ n) j)
    intro x
    convert (hcoeff j x x).star using 1
    · ext n; exact (inner_conj_symm _ _).symm
    · congr 1; exact (inner_conj_symm _ _).symm
  let T : J → TraceClass H := fun j =>
    TraceClass.ofOperator (normalPartOp (f j)) (hex j).2.choose
  refine ⟨T, ?_, φ, hφ, hcoeff⟩
  intro j
  exact ⟨(hex j).1, (hex j).2.choose_spec⟩

end
end Cloning.InfiniteTraceClass
