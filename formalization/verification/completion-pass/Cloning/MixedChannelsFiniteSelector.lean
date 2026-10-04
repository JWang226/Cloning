import Cloning.MixedChannelsFiniteInstrument

/-! A genuine hybrid-to-quantum channel obtained by reading a finite
classical selector, applying its chosen quantum channel, and integrating.
The selector may be any nonnegative measurable partition of unity, including
the indicators of a finite cell partition with an outside fallback. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators Classical
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι]

theorem weightedL1Integral_blockPositive (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hχ0 : ∀ y, 0 ≤ χ y)
    {C : ℝ} (hbound : ∀ y, ‖χ y‖ ≤ C) {n : ℕ}
    (A : Fin n → Fin n → Lp (TraceClass H) 1 μ) (hA : L1BlockPositive A) :
    BlockPositive (fun i j ↦ weightedL1Integral χ hχ hbound (A i j)) := by
  intro v
  let F (i j : Fin n) (y : Ω) : TraceClass H := (χ y : ℂ) • A i j y
  have hF (i j : Fin n) : Integrable (F i j) μ := weightedL1_integrable χ hχ hbound _
  have hi (i j : Fin n) : Integrable (fun y ↦ ⟪v i, (F i j y).1 (v j)⟫_ℂ) μ :=
    (traceClassMatrixCoefficient (v i) (v j)).integrable_comp (hF i j)
  have hs : Integrable (fun y ↦ ∑ i : Fin n, ∑ j : Fin n,
      ⟪v i, (F i j y).1 (v j)⟫_ℂ) μ :=
    integrable_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hi i j))
  have hn : ∀ᵐ y ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ⟪v i, (F i j y).1 (v j)⟫_ℂ := by
    filter_upwards [hA] with y hy
    change 0 ≤ ∑ i, ∑ j, ⟪v i, ((χ y : ℂ) • (A i j y).1) (v j)⟫_ℂ
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum]
    exact mul_nonneg (by exact_mod_cast hχ0 y) (hy v)
  have he (i j : Fin n) :
      ⟪v i, (weightedL1Integral χ hχ hbound (A i j)).1 (v j)⟫_ℂ =
        ∫ y, ⟪v i, (F i j y).1 (v j)⟫_ℂ ∂μ :=
    ((traceClassMatrixCoefficient (v i) (v j)).integral_comp_comm (hF i j)).symm
  simp_rw [he]
  have h := integral_complex_nonneg_ae hs hn
  rw [integral_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hi i j))] at h
  simp_rw [integral_finset_sum _ (fun j _ ↦ hi _ j)] at h
  exact h

theorem finite_blockPositive_sum {n : ℕ} (A : ι → Fin n → Fin n → TraceClass K)
    (hA : ∀ r, BlockPositive (A r)) : BlockPositive (fun i j ↦ ∑ r, A r i j) := by
  intro v
  have hs := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) ↦ hA r v)
  change 0 ≤ ∑ i, ∑ j, ⟪v i, inclusionCLM (∑ r, A r i j) (v j)⟫_ℂ
  simp only [map_sum, ContinuousLinearMap.sum_apply, inner_sum, inclusionCLM_apply]
  have he : (∑ i, ∑ j, ∑ r, ⟪v i, (A r i j).1 (v j)⟫_ℂ) =
      ∑ r, ∑ i, ∑ j, ⟪v i, (A r i j).1 (v j)⟫_ℂ := by
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [he]
  exact hs

variable (χ : ι → Ω → ℝ) (hχ : ∀ r, AEStronglyMeasurable (χ r) μ)
    (hχ0 : ∀ r y, 0 ≤ χ r y) (hχsum : ∀ y, ∑ r, χ r y = 1)
    (Φ : ι → QuantumChannel H K)

include hχ0 hχsum in
theorem finiteSelector_weight_bound (r : ι) (y : Ω) : ‖χ r y‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (hχ0 r y)]
  calc
    χ r y ≤ ∑ k, χ k y := Finset.single_le_sum (fun k _ ↦ hχ0 k y) (Finset.mem_univ r)
    _ = 1 := hχsum y

def finiteSelectorCLM : Lp (TraceClass H) 1 μ →L[ℂ] TraceClass K :=
  ∑ r, (Φ r).toPositiveTracePreservingMap.toContinuousLinearMap.comp
    (weightedL1IntegralCLM (χ r) (hχ r) (finiteSelector_weight_bound χ hχ0 hχsum r))

theorem finiteSelectorCLM_apply (A : Lp (TraceClass H) 1 μ) :
    finiteSelectorCLM χ hχ hχ0 hχsum Φ A =
      ∑ r, (Φ r).toLinearMap (weightedL1Integral (χ r) (hχ r)
        (finiteSelector_weight_bound χ hχ0 hχsum r) A) := by
  simp only [finiteSelectorCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, weightedL1IntegralCLM_apply]
  rfl

theorem finiteSelectorCLM_completelyPositive (n : ℕ)
    (A : Fin n → Fin n → Lp (TraceClass H) 1 μ) (hA : L1BlockPositive A) :
    BlockPositive (fun i j ↦ finiteSelectorCLM χ hχ hχ0 hχsum Φ (A i j)) := by
  simp only [finiteSelectorCLM_apply]
  apply finite_blockPositive_sum
  intro r
  exact (Φ r).completelyPositive n _ (weightedL1Integral_blockPositive
    (χ r) (hχ r) (hχ0 r) (finiteSelector_weight_bound χ hχ0 hχsum r) A hA)

theorem sum_finiteSelector_weighted_integrals (A : Lp (TraceClass H) 1 μ) :
    (∑ r, weightedL1Integral (χ r) (hχ r)
      (finiteSelector_weight_bound χ hχ0 hχsum r) A) = ∫ y, A y ∂μ := by
  change (∑ r, ∫ y, (χ r y : ℂ) • A y ∂μ) = _
  rw [← integral_finset_sum _ (fun r _ ↦ weightedL1_integrable (χ r) (hχ r)
    (finiteSelector_weight_bound χ hχ0 hχsum r) A)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y ↦ by
    dsimp only
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hχsum]
    simp)

theorem finiteSelectorCLM_trace (A : Lp (TraceClass H) 1 μ) :
    traceCLM (finiteSelectorCLM χ hχ hχ0 hχsum Φ A) = integratedTrace A := by
  rw [finiteSelectorCLM_apply, map_sum]
  have ht (r : ι) (B : TraceClass H) : traceCLM ((Φ r).toLinearMap B) = traceCLM B :=
    (Φ r).toPositiveTracePreservingMap.trace_preserving B
  simp_rw [ht]
  rw [← map_sum, sum_finiteSelector_weighted_integrals χ hχ hχ0 hχsum]
  simpa only [HybridToQuantum.integrate_apply] using (HybridToQuantum.integrate.tracePreserving A)

/-- Read a finite classical selector and apply its chosen quantum channel.
This map is CP at every finite ancilla and trace preserving on all L1 inputs. -/
def HybridToQuantum.finiteSelector : HybridToQuantum H K μ where
  map := finiteSelectorCLM χ hχ hχ0 hχsum Φ
  completelyPositive := finiteSelectorCLM_completelyPositive χ hχ hχ0 hχsum Φ
  tracePreserving := finiteSelectorCLM_trace χ hχ hχ0 hχsum Φ

@[simp] theorem HybridToQuantum.finiteSelector_apply (A : Lp (TraceClass H) 1 μ) :
    (HybridToQuantum.finiteSelector χ hχ hχ0 hχsum Φ).map A =
      ∑ r, (Φ r).toLinearMap (weightedL1Integral (χ r) (hχ r)
        (finiteSelector_weight_bound χ hχ0 hχsum r) A) :=
  finiteSelectorCLM_apply χ hχ hχ0 hχsum Φ A

end Cloning.Hybrid
