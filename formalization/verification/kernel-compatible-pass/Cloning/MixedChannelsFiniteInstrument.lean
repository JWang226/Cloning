import Cloning.MixedChannelsPreparation
import Cloning.InfiniteRectangularKraus

/-! Actual finite quantum instruments with a classical density attached to
each outcome. Complete positivity and trace preservation hold on all inputs.
Finite normalized Kraus families give concrete instances of the construction. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators Classical
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι]

theorem Lp_finset_sum_ae {E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (A : ι → Lp E 1 μ) :
    (fun y ↦ (∑ r ∈ s, A r : Lp E 1 μ) y) =ᵐ[μ] fun y ↦ ∑ r ∈ s, A r y := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero E 1 μ)
  | @insert r s hrs ih =>
    rw [Finset.sum_insert hrs]
    filter_upwards [Lp.coeFn_add (A r) (∑ k ∈ s, A k), ih] with y hy hs
    simp only [hy, Pi.add_apply, hs, Finset.sum_insert hrs]

variable (I : ι → TraceClass H →ₗ[ℂ] TraceClass K)
    (hI : ∀ r, IsCompletelyPositive (I r))
    (htrace : ∀ A, ∑ r, traceCLM (I r A) = traceCLM A)
    (g : ι → Ω → ℝ) (hg : ∀ r, Integrable (g r) μ)
    (hg0 : ∀ r y, 0 ≤ g r y) (hprob : ∀ r, ∫ y, g r y ∂μ = 1)

def finiteInstrumentLinearMap : TraceClass H →ₗ[ℂ] Lp (TraceClass K) 1 μ :=
  ∑ r, (prepareL1 (g r) (hg r)).comp (I r)

theorem finiteInstrumentLinearMap_apply (A : TraceClass H) :
    finiteInstrumentLinearMap I g hg A = ∑ r, prepareL1 (g r) (hg r) (I r A) := by
  simp [finiteInstrumentLinearMap]

theorem finiteInstrumentLinearMap_ae (A : TraceClass H) :
    finiteInstrumentLinearMap I g hg A =ᵐ[μ]
      fun y ↦ ∑ r, (g r y : ℂ) • I r A := by
  rw [finiteInstrumentLinearMap_apply]
  have hall : ∀ᵐ y ∂μ, ∀ r, prepareL1 (g r) (hg r) (I r A) y =
      (g r y : ℂ) • I r A := ae_all_iff.mpr (fun r ↦ prepareL1_ae _ _ _)
  filter_upwards [Lp_finset_sum_ae Finset.univ (fun r ↦ prepareL1 (g r) (hg r) (I r A)),
    hall] with y hy hall
  rw [hy]
  exact Finset.sum_congr rfl (fun r _ ↦ hall r)

include hI hg0 in
theorem finiteInstrumentLinearMap_completelyPositive (n : ℕ)
    (A : Fin n → Fin n → TraceClass H) (hA : BlockPositive A) :
    L1BlockPositive (fun i j ↦ finiteInstrumentLinearMap I g hg (A i j)) := by
  have hall : ∀ᵐ y ∂μ, ∀ i j : Fin n,
      finiteInstrumentLinearMap I g hg (A i j) y =
        ∑ r, (g r y : ℂ) • I r (A i j) :=
    ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun j ↦ finiteInstrumentLinearMap_ae I g hg _))
  filter_upwards [hall] with y hy
  intro v
  have hr (r : ι) : 0 ≤ (g r y : ℂ) *
      (∑ i, ∑ j, ⟪v i, (I r (A i j)).1 (v j)⟫_ℂ) :=
    mul_nonneg (by exact_mod_cast hg0 r y) (hI r n A hA v)
  have hs := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) ↦ hr r)
  simp only [hy]
  change 0 ≤ ∑ i, ∑ j, ⟪v i, inclusionCLM (∑ r, (g r y : ℂ) • I r (A i j)) (v j)⟫_ℂ
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right, inclusionCLM_apply]
  have he : (∑ i, ∑ j, ∑ r, (g r y : ℂ) * ⟪v i, (I r (A i j)).1 (v j)⟫_ℂ) =
      ∑ r, ∑ i, ∑ j, (g r y : ℂ) * ⟪v i, (I r (A i j)).1 (v j)⟫_ℂ := by
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [he]
  simpa only [Finset.mul_sum] using hs

include htrace hprob in
theorem finiteInstrumentLinearMap_trace (A : TraceClass H) :
    integratedTrace (finiteInstrumentLinearMap I g hg A) = traceCLM A := by
  rw [finiteInstrumentLinearMap_apply, map_sum]
  calc
    _ = ∑ r, traceCLM (I r A) := by
      apply Finset.sum_congr rfl
      intro r _
      exact (integratedTrace_apply _).trans (integral_trace_prepareL1 _ _ (hprob r) _)
    _ = _ := htrace A

include hI htrace hg0 hprob in
theorem finiteInstrumentLinearMap_norm_nonneg (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖finiteInstrumentLinearMap I g hg A‖ ≤ ‖A‖ := by
  rw [finiteInstrumentLinearMap_apply]
  calc
    _ ≤ ∑ r, ‖prepareL1 (g r) (hg r) (I r A)‖ := norm_sum_le _ _
    _ = ∑ r, (traceCLM (I r A)).re := by
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_prepareL1 _ _ (hg0 r) (hprob r)]
      exact TraceClass.norm_eq_trace_re_of_nonneg _ ((hI r).map_nonneg A hA)
    _ = (traceCLM A).re := by rw [← Complex.re_sum, htrace]
    _ = ‖A‖ := (TraceClass.norm_eq_trace_re_of_nonneg _ hA).symm

def QuantumToHybrid.finiteInstrument : QuantumToHybrid H K μ where
  map := (finiteInstrumentLinearMap I g hg).mkContinuous 2 (fun A ↦ by
    simpa only [mul_one] using norm_map_two_mul_of_positive_bound
      (finiteInstrumentLinearMap I g hg) (by norm_num : (0 : ℝ) ≤ 1)
      (fun B hB ↦ by simpa only [one_mul] using
        finiteInstrumentLinearMap_norm_nonneg I hI htrace g hg hg0 hprob B hB) A)
  completelyPositive := finiteInstrumentLinearMap_completelyPositive I hI g hg hg0
  tracePreserving := finiteInstrumentLinearMap_trace I htrace g hg hprob

@[simp] theorem QuantumToHybrid.finiteInstrument_apply (A : TraceClass H) :
    (QuantumToHybrid.finiteInstrument I hI htrace g hg hg0 hprob).map A =
      ∑ r, prepareL1 (g r) (hg r) (I r A) := finiteInstrumentLinearMap_apply I g hg A

/-- Literal finite Kraus normalization supplies the instrument trace law. -/
def QuantumToHybrid.finiteKrausInstrument (B : ι → H →L[ℂ] K)
    (hB : RectangularKrausComplete B) : QuantumToHybrid H K μ :=
  QuantumToHybrid.finiteInstrument (fun r ↦ conjugationLinearMap (B r))
    (fun r ↦ conjugationLinearMap_completelyPositive (B r))
    (fun A ↦ by
      simpa only [rectangularKrausLinearMap_apply, tsum_fintype, map_sum] using
        rectangularKrausLinearMap_trace B hB A) g hg hg0 hprob

end Cloning.Hybrid
