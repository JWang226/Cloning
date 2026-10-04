import Cloning.MixedChannels

/-! Quantum-to-hybrid fidelity data processing from a single attained
quantum block witness. No pointwise optimizer or measurable selection is assumed. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem QuantumToHybrid.map_isSelfAdjoint (T : QuantumToHybrid H K μ)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    ∀ᵐ y ∂μ, IsSelfAdjoint (T.map A y).1 := by
  have hd : T.map A = T.map (TraceClass.positivePart A hA) -
      T.map (TraceClass.negativePart A hA) := by
    rw [← map_sub, TraceClass.positivePart_sub_negativePart]
  rw [hd]
  filter_upwards [T.map_nonneg _ (TraceClass.positivePart_nonneg A hA),
    T.map_nonneg _ (TraceClass.negativePart_nonneg A hA),
    Lp.coeFn_sub (T.map (TraceClass.positivePart A hA))
      (T.map (TraceClass.negativePart A hA))] with y hp hn he
  rw [he]
  exact (IsSelfAdjoint.of_nonneg hp).sub (IsSelfAdjoint.of_nonneg hn)

/-- Positivity and complex linearity force pointwise adjoint preservation a.e. -/
theorem QuantumToHybrid.map_adjoint (T : QuantumToHybrid H K μ) (A : TraceClass H) :
    ∀ᵐ y ∂μ, T.map (TraceClass.adjoint A) y = TraceClass.adjoint (T.map A y) := by
  let R := T.map (TraceClass.realComponent A)
  let I := T.map (TraceClass.imaginaryComponent A)
  have hsum : T.map A = R + Complex.I • I := by
    dsimp only [R, I]
    rw [← map_smul, ← map_add, TraceClass.realComponent_add_I_smul_imaginaryComponent]
  have hsub : T.map (TraceClass.adjoint A) = R - Complex.I • I := by
    dsimp only [R, I]
    rw [← map_smul, ← map_sub, TraceClass.realComponent_sub_I_smul_imaginaryComponent]
  rw [hsum, hsub]
  filter_upwards [T.map_isSelfAdjoint _ (TraceClass.realComponent_isSelfAdjoint A),
    T.map_isSelfAdjoint _ (TraceClass.imaginaryComponent_isSelfAdjoint A),
    Lp.coeFn_add R (Complex.I • I), Lp.coeFn_sub R (Complex.I • I),
    Lp.coeFn_smul Complex.I I] with y hr hi hadd hsub hsmul
  simp only [hadd, hsub, hsmul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  apply Subtype.ext
  change (R y).1 - Complex.I • (I y).1 = star ((R y).1 + Complex.I • (I y).1)
  rw [star_add, star_smul, hr, hi]
  simp [sub_eq_add_neg, R, I]

theorem QuantumToHybrid.fidelityBlock (T : QuantumToHybrid H K μ) (A B X : TraceClass H)
    (hblock : BlockPositive (InfiniteFidelity.fidelityBlock A B X)) :
    ∀ᵐ y ∂μ, BlockPositive
      (InfiniteFidelity.fidelityBlock (T.map A y) (T.map B y) (T.map X y)) := by
  filter_upwards [T.completelyPositive 2 _ hblock, T.map_adjoint X] with y hp ha
  have he : InfiniteFidelity.fidelityBlock (T.map A y) (T.map B y) (T.map X y) =
      fun i j => T.map (InfiniteFidelity.fidelityBlock A B X i j) y := by
    funext i j
    dsimp only [InfiniteFidelity.fidelityBlock]
    split_ifs <;> try rfl
    exact ha.symm
  rwa [he]

/-- Quantum root fidelity cannot decrease under a genuine quantum-to-hybrid channel. -/
theorem QuantumToHybrid.fidelity_data_processing (T : QuantumToHybrid H K μ)
    (A B : PositiveTraceClass H) :
    A.rootFidelity B ≤ (T.mapPositive A).rootFidelity (T.mapPositive B) := by
  obtain ⟨X, hblock, htrace⟩ := exists_fidelityBlock_witness A.1 B.1 A.2 B.2
  have hTX : Integrable (fun y => (traceCLM (T.map X y)).re) μ :=
    Complex.reCLM.integrable_comp (traceCLM.integrable_comp (L1.integrable_coeFn (T.map X)))
  have ht : (traceCLM X).re = ∫ y, (traceCLM (T.map X y)).re ∂μ := by
    calc
      _ = (∫ y, traceCLM (T.map X y) ∂μ).re := by
        rw [← integratedTrace_apply, T.tracePreserving]
      _ = _ := (Complex.reCLM.integral_comp_comm
        (traceCLM.integrable_comp (L1.integrable_coeFn (T.map X)))).symm
  change InfiniteFidelity.fidelity A.1.1 B.1.1 A.2 B.2 A.1.2 B.1.2 ≤ _
  rw [← htrace, ht, PositiveL1.rootFidelity_eq_integral]
  apply integral_mono_ae hTX ((T.mapPositive A).integrable_rootFidelity (T.mapPositive B))
  filter_upwards [T.map_nonneg A.1 A.2, T.map_nonneg B.1 B.2,
    T.fidelityBlock A.1 B.1 X hblock] with y hA hB hp
  change (traceCLM (T.map X y)).re ≤ extendedRootFidelity (T.map A.1 y, T.map B.1 y)
  rw [extendedRootFidelity_eq _ _ hA hB]
  exact trace_re_le_fidelity_of_block _ _ _ hA hB (fidelityBlock_quadratic _ _ _ hp)

end Cloning.Hybrid
