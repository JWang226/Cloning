import Cloning.HybridL1Fidelity

/-! Joint concavity and Bochner Jensen for fidelity on the positive
operator-valued L1 cone. This applies directly to continuous hybrid channels. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coeFn_Lp_add_smul (A B : Lp (TraceClass H) 1 μ) (a b : ℝ) :
    (a • A + b • B : Lp (TraceClass H) 1 μ) =ᵐ[μ]
      fun y => a • A y + b • B y := by
  filter_upwards [Lp.coeFn_add (a • A) (b • B), Lp.coeFn_smul a A,
    Lp.coeFn_smul b B] with y hadd ha hb
  simp only [hadd, Pi.add_apply, ha, hb, Pi.smul_apply]

def positiveL1Pairs : Set (Lp (TraceClass H) 1 μ × Lp (TraceClass H) 1 μ) :=
  {p | (∀ᵐ y ∂μ, 0 ≤ (p.1 y).1) ∧ (∀ᵐ y ∂μ, 0 ≤ (p.2 y).1)}

def extendedL1RootFidelity (p : Lp (TraceClass H) 1 μ × Lp (TraceClass H) 1 μ) : ℝ := by
  classical
  exact if h : p ∈ positiveL1Pairs then
    PositiveL1.rootFidelity ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 0

theorem extendedL1RootFidelity_eq (A B : PositiveL1 H μ) :
    extendedL1RootFidelity (A.1, B.1) = A.rootFidelity B := by
  unfold extendedL1RootFidelity
  rw [dif_pos (show (A.1, B.1) ∈ positiveL1Pairs from ⟨A.2, B.2⟩)]
  rfl

theorem extendedL1RootFidelity_eq_integral
    {p : Lp (TraceClass H) 1 μ × Lp (TraceClass H) 1 μ} (hp : p ∈ positiveL1Pairs) :
    extendedL1RootFidelity p = ∫ y, extendedRootFidelity (p.1 y, p.2 y) ∂μ := by
  rw [show p = (p.1, p.2) from rfl, extendedL1RootFidelity_eq ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩,
    PositiveL1.rootFidelity_eq_integral]

theorem convex_positiveL1Pairs : Convex ℝ (positiveL1Pairs (H := H) (μ := μ)) := by
  intro p hp q hq a b ha hb _
  constructor
  · filter_upwards [hp.1, hq.1, coeFn_Lp_add_smul p.1 q.1 a b] with y hpy hqy hy
    change 0 ≤ ((a • p.1 + b • q.1) y).1
    rw [hy]
    change 0 ≤ a • (p.1 y).1 + b • (q.1 y).1
    exact add_nonneg (smul_nonneg ha hpy) (smul_nonneg hb hqy)
  · filter_upwards [hp.2, hq.2, coeFn_Lp_add_smul p.2 q.2 a b] with y hpy hqy hy
    change 0 ≤ ((a • p.2 + b • q.2) y).1
    rw [hy]
    change 0 ≤ a • (p.2 y).1 + b • (q.2 y).1
    exact add_nonneg (smul_nonneg ha hpy) (smul_nonneg hb hqy)

theorem isClosed_positiveL1Pairs : IsClosed (positiveL1Pairs (H := H) (μ := μ)) := by
  have hs : IsClosed {A : Lp (TraceClass H) 1 μ | ∀ᵐ y ∂μ, 0 ≤ (A y).1} :=
    isClosed_Lp_ae_mem (isClosed_le continuous_const (inclusionCLM (H := H)).continuous)
  exact (hs.preimage continuous_fst).inter (hs.preimage continuous_snd)

theorem continuousOn_extendedL1RootFidelity :
    ContinuousOn (extendedL1RootFidelity (H := H) (μ := μ)) positiveL1Pairs := by
  rw [continuousOn_iff_continuous_restrict]
  let j : positiveL1Pairs (H := H) (μ := μ) → PositiveL1 H μ × PositiveL1 H μ :=
    fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  have hj : Continuous j :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  have h := PositiveL1.continuous_rootFidelity.comp hj
  convert h using 1
  funext p
  exact extendedL1RootFidelity_eq ⟨p.1.1, p.2.1⟩ ⟨p.1.2, p.2.2⟩

/-- Fibrewise infinite-dimensional joint concavity integrates to the actual
L1 fidelity; no commutativity of fibres or classical--quantum independence is used. -/
theorem concaveOn_extendedL1RootFidelity :
    ConcaveOn ℝ (positiveL1Pairs (H := H) (μ := μ)) extendedL1RootFidelity := by
  refine ⟨convex_positiveL1Pairs, ?_⟩
  intro p hp q hq a b ha hb hab
  have hc := convex_positiveL1Pairs hp hq ha hb hab
  have hip := PositiveL1.integrable_rootFidelity (⟨p.1, hp.1⟩ : PositiveL1 H μ) ⟨p.2, hp.2⟩
  have hiq := PositiveL1.integrable_rootFidelity (⟨q.1, hq.1⟩ : PositiveL1 H μ) ⟨q.2, hq.2⟩
  have hic := PositiveL1.integrable_rootFidelity
    (⟨(a • p + b • q).1, hc.1⟩ : PositiveL1 H μ) ⟨(a • p + b • q).2, hc.2⟩
  simp only [smul_eq_mul]
  rw [extendedL1RootFidelity_eq_integral hp, extendedL1RootFidelity_eq_integral hq,
    extendedL1RootFidelity_eq_integral hc, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hip.const_mul a) (hiq.const_mul b)]
  apply integral_mono_ae ((hip.const_mul a).add (hiq.const_mul b)) hic
  filter_upwards [hp.1, hp.2, hq.1, hq.2,
    coeFn_Lp_add_smul p.1 q.1 a b, coeFn_Lp_add_smul p.2 q.2 a b] with y hp₁ hp₂ hq₁ hq₂ h₁ h₂
  change a * extendedRootFidelity (p.1 y, p.2 y) + b * extendedRootFidelity (q.1 y, q.2 y) ≤
    extendedRootFidelity ((a • p.1 + b • q.1) y, (a • p.2 + b • q.2) y)
  rw [h₁, h₂]
  exact concaveOn_extendedRootFidelity.2 ⟨hp₁, hp₂⟩ ⟨hq₁, hq₂⟩ ha hb hab

namespace PositiveL1

variable {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}

theorem integrable_family_rootFidelity (A B : Ξ → PositiveL1 H μ)
    (hA : Integrable (fun ξ => (A ξ).1) ν) (hB : Integrable (fun ξ => (B ξ).1) ν) :
    Integrable (fun ξ => (A ξ).rootFidelity (B ξ)) ν := by
  have hmA : AEStronglyMeasurable A ν :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp hA.aestronglyMeasurable
  have hmB : AEStronglyMeasurable B ν :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp hB.aestronglyMeasurable
  apply (integrable_sqrt_mul_sqrt hA.norm hB.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mono'
    (continuous_rootFidelity.comp_aestronglyMeasurable (hmA.prodMk hmB))
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (rootFidelity_nonneg _ _)]
    exact rootFidelity_le_sqrt _ _

/-- Joint Jensen for any Bochner-integrable probability family of actual
positive L1 states, expressed with arbitrary identified average states. -/
theorem integral_rootFidelity_le [IsProbabilityMeasure ν]
    (A B : Ξ → PositiveL1 H μ)
    (hA : Integrable (fun ξ => (A ξ).1) ν) (hB : Integrable (fun ξ => (B ξ).1) ν)
    (R S : PositiveL1 H μ)
    (hR : R.1 = ∫ ξ, (A ξ).1 ∂ν) (hS : S.1 = ∫ ξ, (B ξ).1 ∂ν) :
    (∫ ξ, (A ξ).rootFidelity (B ξ) ∂ν) ≤ R.rootFidelity S := by
  let f : Ξ → Lp (TraceClass H) 1 μ × Lp (TraceClass H) 1 μ :=
    fun ξ => ((A ξ).1, (B ξ).1)
  have hf : Integrable f ν := hA.prodMk hB
  have hgi : Integrable (extendedL1RootFidelity ∘ f) ν := by
    change Integrable (fun ξ => extendedL1RootFidelity ((A ξ).1, (B ξ).1)) ν
    simpa only [extendedL1RootFidelity_eq] using
      integrable_family_rootFidelity A B hA hB
  have hp : ∀ᵐ ξ ∂ν, f ξ ∈ positiveL1Pairs :=
    Eventually.of_forall fun ξ => And.intro (A ξ).2 (B ξ).2
  have h := (concaveOn_extendedL1RootFidelity (H := H) (μ := μ)).le_map_integral
    (continuousOn_extendedL1RootFidelity (H := H) (μ := μ))
    (isClosed_positiveL1Pairs (H := H) (μ := μ)) hp hf hgi
  change (∫ ξ, extendedL1RootFidelity ((A ξ).1, (B ξ).1) ∂ν) ≤
    extendedL1RootFidelity (∫ ξ, ((A ξ).1, (B ξ).1) ∂ν) at h
  simp only [extendedL1RootFidelity_eq] at h
  rw [integral_pair hA hB, ← hR, ← hS, extendedL1RootFidelity_eq] at h
  exact h

/-- The fixed-target form used for hybrid channel averaging. -/
theorem integral_rootFidelity_const_le [IsProbabilityMeasure ν]
    (A : Ξ → PositiveL1 H μ) (hA : Integrable (fun ξ => (A ξ).1) ν)
    (R B : PositiveL1 H μ) (hR : R.1 = ∫ ξ, (A ξ).1 ∂ν) :
    (∫ ξ, (A ξ).rootFidelity B ∂ν) ≤ R.rootFidelity B := by
  exact integral_rootFidelity_le A (fun _ => B) hA (integrable_const B.1) R B hR (by simp)

end PositiveL1
end Cloning.Hybrid
