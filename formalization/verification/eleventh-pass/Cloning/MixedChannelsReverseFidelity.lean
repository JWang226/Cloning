import Cloning.MixedChannelsPositiveApprox

/-! Reverse mixed-channel fidelity data processing, proved by positive simple
approximation and finitely many attained block witnesses. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem block_adjoint {C : Fin 2 → Fin 2 → TraceClass K}
    (hC : BlockPositive C) (h0 : 0 ≤ (C 0 0).1) (h1 : 0 ≤ (C 1 1).1) :
    C 1 0 = TraceClass.adjoint (C 0 1) := by
  have hsum := IsSelfAdjoint.of_nonneg (hC.scalarCompression ![1, 1])
  have him := IsSelfAdjoint.of_nonneg (hC.scalarCompression ![1, Complex.I])
  have hd0 := (IsSelfAdjoint.of_nonneg h0).star_eq
  have hd1 := (IsSelfAdjoint.of_nonneg h1).star_eq
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    star_one, one_mul, mul_one, one_smul] at hsum him
  change IsSelfAdjoint ((C 0 0).1 + (C 0 1).1 + ((C 1 0).1 + (C 1 1).1)) at hsum
  have hs := hsum.star_eq
  simp only [star_add, hd0, hd1] at hs
  change IsSelfAdjoint ((C 0 0).1 + Complex.I • (C 0 1).1 +
    ((star Complex.I) • (C 1 0).1 + ((star Complex.I) * Complex.I) • (C 1 1).1)) at him
  simp only [Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg,
    one_smul, neg_smul] at him
  have hi := him.star_eq
  simp only [star_add, star_smul, star_neg, Complex.star_def, Complex.conj_I,
    hd0, hd1] at hi
  apply Subtype.ext
  change (C 1 0).1 = star (C 0 1).1
  have hs' : star (C 0 1).1 + star (C 1 0).1 = (C 0 1).1 + (C 1 0).1 := by
    apply add_left_cancel (a := (C 0 0).1 + (C 1 1).1)
    convert hs using 1 <;> module
  have hi' : -Complex.I • star (C 0 1).1 + Complex.I • star (C 1 0).1 =
      Complex.I • (C 0 1).1 - Complex.I • (C 1 0).1 := by
    apply add_left_cancel (a := (C 0 0).1 + (C 1 1).1)
    convert hi using 1 <;> module
  have he := congrArg (fun x : K →L[ℂ] K => Complex.I • x) hi'
  simp only [smul_add, smul_sub, smul_smul, mul_neg, Complex.I_mul_I,
    neg_neg, one_smul, neg_one_smul] at he
  have he' : star (C 0 1).1 - star (C 1 0).1 = -(C 0 1).1 + (C 1 0).1 := by
    simpa only [sub_eq_add_neg, neg_neg] using he
  calc
    (C 1 0).1 = (1 / 2 : ℂ) • (((C 0 1).1 + (C 1 0).1) +
        (-(C 0 1).1 + (C 1 0).1)) := by module
    _ = (1 / 2 : ℂ) • ((star (C 0 1).1 + star (C 1 0).1) +
        (star (C 0 1).1 - star (C 1 0).1)) := by rw [hs', he']
    _ = star (C 0 1).1 := by module

private def fibreWitness (p : TraceClass H × TraceClass H) : TraceClass H := by
  classical
  exact if hp : 0 ≤ p.1.1 ∧ 0 ≤ p.2.1 then polarWitness p.1 p.2 hp.1 hp.2 else 0

private theorem fibreWitness_zero : fibreWitness (0 : TraceClass H × TraceClass H) = 0 := by
  apply Subtype.ext
  simp [fibreWitness, polarWitness, contractionWitness]

private theorem fibreWitness_block (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    BlockPositive (fidelityBlock A B (fibreWitness (A, B))) := by
  simp only [fibreWitness, dif_pos (And.intro hA hB)]
  exact polarWitness_blockPositive A B hA hB

private theorem fibreWitness_trace (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    (traceCLM (fibreWitness (A, B))).re = extendedRootFidelity (A, B) := by
  rw [extendedRootFidelity_eq A B hA hB]
  simp only [fibreWitness, dif_pos (And.intro hA hB)]
  exact polarWitness_trace A B hA hB

private def positiveSimple (f : SimpleFunc Ω (TraceClass H)) (hf : Integrable f μ)
    (hp : ∀ y, 0 ≤ (f y).1) : PositiveL1 H μ :=
  ⟨hf.toL1 f, by
    filter_upwards [hf.coeFn_toL1] with y hy
    rw [hy]
    exact hp y⟩

private theorem simple_data_processing (S : HybridToQuantum H K μ)
    (f g : SimpleFunc Ω (TraceClass H)) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfp : ∀ y, 0 ≤ (f y).1) (hgp : ∀ y, 0 ≤ (g y).1) :
    (positiveSimple f hf hfp).rootFidelity (positiveSimple g hg hgp) ≤
      (S.mapPositive (positiveSimple f hf hfp)).rootFidelity
        (S.mapPositive (positiveSimple g hg hgp)) := by
  let p := f.pair g
  let b (i j : Fin 2) := p.map (fun q => fidelityBlock q.1 q.2 (fibreWitness q) i j)
  have hbi (i j : Fin 2) : Integrable (b i j) μ := by
    apply SimpleFunc.FinMeasSupp.integrable
    apply (SimpleFunc.integrable_iff_finMeasSupp.mp (SimpleFunc.integrable_pair hf hg)).map
    simp only [Prod.fst_zero, Prod.snd_zero, fibreWitness_zero, fidelityBlock]
    split_ifs <;> try rfl
    apply Subtype.ext
    simp [TraceClass.adjoint]
  let C (i j : Fin 2) := (hbi i j).toL1 (b i j)
  have hC : ∀ᵐ y ∂μ, ∀ i j : Fin 2,
      C i j y = fidelityBlock (f y) (g y) (fibreWitness (f y, g y)) i j := by
    exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hbi i j).coeFn_toL1
  have hCp : L1BlockPositive C := by
    filter_upwards [hC] with y hy
    simpa only [hy] using fibreWitness_block (f y) (g y) (hfp y) (hgp y)
  have h00 : C 0 0 = hf.toL1 f := by
    apply Lp.ext
    filter_upwards [hC, hf.coeFn_toL1] with y hy hf'
    rw [hy, hf']
    simp [fidelityBlock]
  have h11 : C 1 1 = hg.toL1 g := by
    apply Lp.ext
    filter_upwards [hC, hg.coeFn_toL1] with y hy hg'
    rw [hy, hg']
    simp [fidelityBlock]
  have hout := S.completelyPositive 2 C hCp
  have hdiag0 : 0 ≤ (S.map (C 0 0)).1 := by
    rw [h00]
    exact (S.mapPositive (positiveSimple f hf hfp)).2
  have hdiag1 : 0 ≤ (S.map (C 1 1)).1 := by
    rw [h11]
    exact (S.mapPositive (positiveSimple g hg hgp)).2
  have hadj := block_adjoint hout hdiag0 hdiag1
  have hblock : BlockPositive (fidelityBlock (S.map (C 0 0)) (S.map (C 1 1))
      (S.map (C 0 1))) := by
    have he : fidelityBlock (S.map (C 0 0)) (S.map (C 1 1)) (S.map (C 0 1)) =
        (fun i j => S.map (C i j)) := by
      funext i j
      fin_cases i <;> fin_cases j <;> simp [fidelityBlock, hadj]
    rwa [he]
  have hbound := trace_re_le_fidelity_of_block _ _ _ hdiag0 hdiag1
    (fidelityBlock_quadratic _ _ _ hblock)
  have ht : (traceCLM (S.map (C 0 1))).re =
      (positiveSimple f hf hfp).rootFidelity (positiveSimple g hg hgp) := by
    rw [S.tracePreserving, integratedTrace_apply, PositiveL1.rootFidelity_eq_integral]
    calc
      _ = ∫ y, (traceCLM (C 0 1 y)).re ∂μ :=
        (Complex.reCLM.integral_comp_comm
          (traceCLM.integrable_comp (L1.integrable_coeFn (C 0 1)))).symm
      _ = _ := ?_
    apply integral_congr_ae
    filter_upwards [hC, hf.coeFn_toL1, hg.coeFn_toL1] with y hy hf' hg'
    change (traceCLM (C 0 1 y)).re = extendedRootFidelity
      ((hf.toL1 f) y, (hg.toL1 g) y)
    rw [hy, hf', hg']
    simpa [fidelityBlock] using fibreWitness_trace (f y) (g y) (hfp y) (hgp y)
  rw [ht] at hbound
  simpa only [h00, h11] using hbound

/-- An actual reverse mixed channel acts continuously on the positive cones. -/
theorem HybridToQuantum.continuous_mapPositive (S : HybridToQuantum H K μ) :
    Continuous S.mapPositive :=
  (S.map.continuous.comp continuous_subtype_val).subtype_mk _

/-- Root fidelity cannot decrease under any actual classical–quantum to quantum
channel. The measure, Hilbert spaces, and integrable positive fields are arbitrary;
there is no measurable optimizer, rank, separability, or finiteness premise. -/
theorem HybridToQuantum.fidelity_data_processing (S : HybridToQuantum H K μ)
    (A B : PositiveL1 H μ) :
    A.rootFidelity B ≤ (S.mapPositive A).rootFidelity (S.mapPositive B) := by
  obtain ⟨f, hf, hfp, hft⟩ := A.exists_simple_approx
  obtain ⟨g, hg, hgp, hgt⟩ := B.exists_simple_approx
  let a n := positiveSimple (f n) (hf n) (hfp n)
  let b n := positiveSimple (g n) (hg n) (hgp n)
  have ha : Tendsto a atTop (𝓝 A) := tendsto_subtype_rng.mpr hft
  have hb : Tendsto b atTop (𝓝 B) := tendsto_subtype_rng.mpr hgt
  have hleft := PositiveL1.continuous_rootFidelity.tendsto (A, B) |>.comp
    (ha.prodMk_nhds hb)
  have hright := PositiveTraceClass.continuous_rootFidelity.tendsto
    (S.mapPositive A, S.mapPositive B) |>.comp
      (((S.continuous_mapPositive.tendsto A).comp ha).prodMk_nhds
        ((S.continuous_mapPositive.tendsto B).comp hb))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n =>
    simple_data_processing S (f n) (g n) (hf n) (hg n) (hfp n) (hgp n))

end Cloning.Hybrid
