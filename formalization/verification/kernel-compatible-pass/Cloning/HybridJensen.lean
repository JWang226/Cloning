import Cloning.HybridL1
import Cloning.InfiniteFidelityConcavity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Jensen's inequality for infinite-dimensional quantum fidelity

Root fidelity of Bochner mixtures dominates the average root fidelity.
No measurable choice of Uhlmann optimizers is assumed: finite joint concavity
and trace-norm continuity feed the Banach-space Jensen theorem.
-/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive-pair domain of quantum fidelity in a real Banach space. -/
def positivePairs : Set (TraceClass H × TraceClass H) :=
  {p | 0 ≤ p.1.1 ∧ 0 ≤ p.2.1}

/-- A total extension used only to state ordinary Banach-space Jensen. Its
value outside the positive cone plays no role in any theorem. -/
def extendedRootFidelity (p : TraceClass H × TraceClass H) : ℝ := by
  classical
  exact if h : p ∈ positivePairs then
    PositiveTraceClass.rootFidelity ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 0

lemma extendedRootFidelity_eq (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    extendedRootFidelity (A, B) = fidelity A.1 B.1 hA hB A.2 B.2 := by
  unfold extendedRootFidelity
  rw [dif_pos (show (A, B) ∈ positivePairs from ⟨hA, hB⟩)]
  rfl

lemma convex_positivePairs : Convex ℝ (positivePairs (H := H)) := by
  intro p hp q hq a b ha hb hab
  constructor
  · change 0 ≤ a • p.1.1 + b • q.1.1
    exact add_nonneg (smul_nonneg ha hp.1) (smul_nonneg hb hq.1)
  · change 0 ≤ a • p.2.1 + b • q.2.1
    exact add_nonneg (smul_nonneg ha hp.2) (smul_nonneg hb hq.2)

lemma isClosed_positivePairs : IsClosed (positivePairs (H := H)) := by
  have h1 : IsClosed {p : TraceClass H × TraceClass H | 0 ≤ p.1.1} :=
    isClosed_le continuous_const (inclusionCLM.continuous.comp continuous_fst)
  have h2 : IsClosed {p : TraceClass H × TraceClass H | 0 ≤ p.2.1} :=
    isClosed_le continuous_const (inclusionCLM.continuous.comp continuous_snd)
  exact h1.inter h2

lemma continuousOn_extendedRootFidelity :
    ContinuousOn (extendedRootFidelity (H := H)) positivePairs := by
  rw [continuousOn_iff_continuous_restrict]
  let j : positivePairs (H := H) → PositiveTraceClass H × PositiveTraceClass H :=
    fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  have hj : Continuous j := by
    apply Continuous.prodMk
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have h := PositiveTraceClass.continuous_rootFidelity.comp hj
  convert h using 1
  funext p
  exact extendedRootFidelity_eq _ _ p.2.1 p.2.2

/-- The actual positive trace-class fidelity is jointly concave on its full
Banach-space domain. -/
theorem concaveOn_extendedRootFidelity :
    ConcaveOn ℝ (positivePairs (H := H)) extendedRootFidelity := by
  refine ⟨convex_positivePairs, ?_⟩
  intro p hp q hq a b ha hb hab
  have hc := convex_positivePairs hp hq ha hb hab
  rw [extendedRootFidelity_eq p.1 p.2 hp.1 hp.2,
    extendedRootFidelity_eq q.1 q.2 hq.1 hq.2]
  have he := extendedRootFidelity_eq (a • p.1 + b • q.1)
    (a • p.2 + b • q.2) hc.1 hc.2
  change a * _ + b * _ ≤ extendedRootFidelity (a • p.1 + b • q.1, a • p.2 + b • q.2)
  rw [he]
  simpa only [Complex.coe_smul] using
    fidelity_weighted_joint_concavity p.1 p.2 q.1 q.2 hp.1 hp.2 hq.1 hq.2 a b ha hb

lemma positivePairs_smul {p : TraceClass H × TraceClass H} (hp : p ∈ positivePairs)
    {a : ℝ} (ha : 0 ≤ a) : a • p ∈ positivePairs := by
  constructor
  · change 0 ≤ a • p.1.1
    exact smul_nonneg ha hp.1
  · change 0 ≤ a • p.2.1
    exact smul_nonneg ha hp.2

lemma extendedRootFidelity_smul_ge {p : TraceClass H × TraceClass H}
    (hp : p ∈ positivePairs) {a : ℝ} (ha : 0 ≤ a) :
    a * extendedRootFidelity p ≤ extendedRootFidelity (a • p) := by
  rw [extendedRootFidelity_eq p.1 p.2 hp.1 hp.2]
  have h := fidelity_weighted_joint_concavity p.1 p.2 p.1 p.2
    hp.1 hp.2 hp.1 hp.2 a 0 ha le_rfl
  have he := extendedRootFidelity_eq (a • p.1) (a • p.2)
    (positivePairs_smul hp ha).1 (positivePairs_smul hp ha).2
  change _ ≤ extendedRootFidelity (a • p.1, a • p.2)
  rw [he]
  simpa only [zero_smul, add_zero, zero_mul, Complex.coe_smul] using h

/-- Common nonnegative scaling is exactly homogeneous, even for singular
infinite-dimensional trace-class states. -/
lemma extendedRootFidelity_smul {p : TraceClass H × TraceClass H}
    (hp : p ∈ positivePairs) {a : ℝ} (ha : 0 ≤ a) :
    extendedRootFidelity (a • p) = a * extendedRootFidelity p := by
  by_cases hzero : a = 0
  · subst a
    simp only [zero_smul, zero_mul]
    rw [show (0 : TraceClass H × TraceClass H) = (0, 0) from rfl,
      extendedRootFidelity_eq _ _ le_rfl le_rfl]
    exact (fidelity_self le_rfl isTraceClass_zero).trans ((trace_re_eq_traceNorm le_rfl isTraceClass_zero).trans traceNorm_zero)
  · apply le_antisymm _ (extendedRootFidelity_smul_ge hp ha)
    have h := extendedRootFidelity_smul_ge (positivePairs_smul hp ha)
      (inv_nonneg.mpr ha)
    rw [inv_smul_smul₀ hzero] at h
    have hm := mul_le_mul_of_nonneg_left h ha
    simpa only [← mul_assoc, mul_inv_cancel₀ hzero, one_mul] using hm

namespace PositiveField

/-- Quantum fidelity increases when a probability-valued classical register is
forgotten. This holds for arbitrary, noncommuting, infinite-dimensional fibres. -/
theorem rootFidelity_le_marginal [IsProbabilityMeasure μ]
    (R S : PositiveField (H := H) μ) :
    R.rootFidelity S ≤ fidelity R.quantumMarginal.1 S.quantumMarginal.1
      R.quantumMarginal_nonneg S.quantumMarginal_nonneg R.quantumMarginal.2 S.quantumMarginal.2 := by
  let f : Ω → TraceClass H × TraceClass H := fun x => ((R.value x).1, (S.value x).1)
  have he (x : Ω) : extendedRootFidelity (f x) =
      PositiveTraceClass.rootFidelity (R.value x) (S.value x) :=
    extendedRootFidelity_eq _ _ (R.value x).2 (S.value x).2
  have hfi : Integrable f μ := R.integrable.prodMk S.integrable
  have hgi : Integrable (extendedRootFidelity ∘ f) μ := by
    change Integrable (fun x => extendedRootFidelity (f x)) μ
    simpa only [he] using R.integrable_rootFidelity S
  have h := concaveOn_extendedRootFidelity.le_map_integral
    continuousOn_extendedRootFidelity isClosed_positivePairs
    (Eventually.of_forall fun x => And.intro (R.value x).2 (S.value x).2) hfi hgi
  simp only [he] at h
  change R.rootFidelity S ≤ extendedRootFidelity (∫ x, ((R.value x).1, (S.value x).1) ∂μ) at h
  rw [integral_pair R.integrable S.integrable] at h
  change R.rootFidelity S ≤ extendedRootFidelity (R.quantumMarginal, S.quantumMarginal) at h
  rwa [extendedRootFidelity_eq _ _ R.quantumMarginal_nonneg S.quantumMarginal_nonneg] at h

/-- Homogeneity removes the normalization of the classical base measure. -/
theorem rootFidelity_le_marginal_finite [IsFiniteMeasure μ]
    (R S : PositiveField (H := H) μ) :
    R.rootFidelity S ≤ fidelity R.quantumMarginal.1 S.quantumMarginal.1
      R.quantumMarginal_nonneg S.quantumMarginal_nonneg R.quantumMarginal.2 S.quantumMarginal.2 := by
  rw [← extendedRootFidelity_eq R.quantumMarginal S.quantumMarginal
    R.quantumMarginal_nonneg S.quantumMarginal_nonneg]
  by_cases hzero : μ = 0
  · simp only [rootFidelity, quantumMarginal, hzero, integral_zero_measure]
    rw [extendedRootFidelity_eq 0 0 le_rfl le_rfl]
    exact le_of_eq ((fidelity_self le_rfl isTraceClass_zero).trans
      ((trace_re_eq_traceNorm le_rfl isTraceClass_zero).trans traceNorm_zero)).symm
  letI : NeZero μ := ⟨hzero⟩
  let f : Ω → TraceClass H × TraceClass H := fun x => ((R.value x).1, (S.value x).1)
  have he (x : Ω) : extendedRootFidelity (f x) =
      PositiveTraceClass.rootFidelity (R.value x) (S.value x) :=
    extendedRootFidelity_eq _ _ (R.value x).2 (S.value x).2
  have hfi : Integrable f μ := R.integrable.prodMk S.integrable
  have hgi : Integrable (extendedRootFidelity ∘ f) μ := by
    change Integrable (fun x => extendedRootFidelity (f x)) μ
    simpa only [he] using R.integrable_rootFidelity S
  have h := concaveOn_extendedRootFidelity.le_map_average
    continuousOn_extendedRootFidelity isClosed_positivePairs
    (Eventually.of_forall fun x => And.intro (R.value x).2 (S.value x).2) hfi hgi
  simp only [average_eq, he] at h
  dsimp only [f] at h
  rw [integral_pair R.integrable S.integrable] at h
  change (μ.real Set.univ)⁻¹ * R.rootFidelity S ≤
    extendedRootFidelity ((μ.real Set.univ)⁻¹ • (R.quantumMarginal, S.quantumMarginal)) at h
  rw [extendedRootFidelity_smul (p := (R.quantumMarginal, S.quantumMarginal))
    (a := (μ.real Set.univ)⁻¹)
    ⟨R.quantumMarginal_nonneg, S.quantumMarginal_nonneg⟩ (by positivity)] at h
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr (measureReal_univ_pos (μ := μ)))).mp h

end PositiveField
end Cloning.Hybrid
