import Cloning.InfiniteFidelityContinuity
import Cloning.InfiniteTraceClassChannels
import Cloning.InfiniteTraceClassSeries
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuous classical registers with trace-class quantum fibres

A hybrid positive state is an integrable field of positive trace-class
operators. Positivity is intrinsic in the fibre type; measurable fidelity is
proved from its trace-norm continuity, rather than assumed for every pair.
The base measure may be infinite (in particular Lebesgue measure).
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass Cloning.InfiniteFidelity

namespace Cloning.Hybrid

set_option backward.isDefEq.respectTransparency false

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The closed positive cone of the genuine trace-class Banach space. -/
def PositiveTraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := { A : TraceClass H // 0 ≤ A.1 }

namespace PositiveTraceClass

instance : TopologicalSpace (PositiveTraceClass H) := inferInstanceAs
  (TopologicalSpace { A : TraceClass H // 0 ≤ A.1 })
instance : MetricSpace (PositiveTraceClass H) := inferInstanceAs
  (MetricSpace { A : TraceClass H // 0 ≤ A.1 })

/-- Root fidelity of two positive trace-class fibres. -/
def rootFidelity (A B : PositiveTraceClass H) : ℝ :=
  fidelity A.1.1 B.1.1 A.2 B.2 A.1.2 B.1.2

lemma rootFidelity_nonneg (A B : PositiveTraceClass H) : 0 ≤ rootFidelity A B :=
  fidelity_nonneg A.2 B.2 A.1.2 B.1.2

lemma rootFidelity_comm (A B : PositiveTraceClass H) :
    rootFidelity A B = rootFidelity B A := fidelity_comm A.2 B.2 A.1.2 B.1.2

lemma rootFidelity_self (A : PositiveTraceClass H) : rootFidelity A A = ‖A.1‖ := by
  exact (fidelity_self A.2 A.1.2).trans (TraceClass.norm_eq_trace_re_of_nonneg A.1 A.2).symm

lemma rootFidelity_le_sqrt (A B : PositiveTraceClass H) :
    rootFidelity A B ≤ Real.sqrt ‖A.1‖ * Real.sqrt ‖B.1‖ := by
  simpa only [TraceClass.norm_eq_trace_re_of_nonneg A.1 A.2,
    TraceClass.norm_eq_trace_re_of_nonneg B.1 B.2] using
    fidelity_le_sqrt_mul_sqrt A.2 B.2 A.1.2 B.1.2

lemma rootFidelity_continuity (A B C D : PositiveTraceClass H) :
    |rootFidelity A B - rootFidelity C D| ≤
      Real.sqrt ‖A.1 - C.1‖ * Real.sqrt ‖B.1‖ +
      Real.sqrt ‖B.1 - D.1‖ * Real.sqrt ‖C.1‖ := by
  simpa only [TraceClass.norm_eq_trace_re_of_nonneg B.1 B.2,
    TraceClass.norm_eq_trace_re_of_nonneg C.1 C.2] using
    fidelity_continuity A.2 B.2 C.2 D.2 A.1.2 B.1.2 C.1.2 D.1.2

/-- The analytic root fidelity is continuous on the positive trace-class cone. -/
theorem continuous_rootFidelity :
    Continuous (fun p : PositiveTraceClass H × PositiveTraceClass H =>
      rootFidelity p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have hA : Tendsto (fun q : PositiveTraceClass H × PositiveTraceClass H => q.1.1)
      (𝓝 p) (𝓝 p.1.1) := continuous_subtype_val.continuousAt.comp
        continuous_fst.continuousAt
  have hB : Tendsto (fun q : PositiveTraceClass H × PositiveTraceClass H => q.2.1)
      (𝓝 p) (𝓝 p.2.1) := continuous_subtype_val.continuousAt.comp
        continuous_snd.continuousAt
  have hlim : Tendsto
      (fun q : PositiveTraceClass H × PositiveTraceClass H =>
        Real.sqrt ‖q.1.1 - p.1.1‖ * Real.sqrt ‖q.2.1‖ +
        Real.sqrt ‖q.2.1 - p.2.1‖ * Real.sqrt ‖p.1.1‖) (𝓝 p) (𝓝 0) := by
    convert (((hA.sub tendsto_const_nhds).norm.sqrt).mul hB.norm.sqrt).add
      (((hB.sub tendsto_const_nhds).norm.sqrt).mul tendsto_const_nhds) using 1 <;>
      simp
  exact squeeze_zero (fun q => norm_nonneg _) (fun q => by
    simpa only [Real.norm_eq_abs] using rootFidelity_continuity q.1 q.2 p.1 p.2) hlim

/-- Positive trace-preserving maps act continuously on the positive cone. -/
def map (Φ : PositiveTracePreservingMap H K) (A : PositiveTraceClass H) :
    PositiveTraceClass K := ⟨Φ A.1, Φ.map_nonneg A.1 A.2⟩

lemma continuous_map (Φ : PositiveTracePreservingMap H K) : Continuous (map Φ) := by
  exact (Φ.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma norm_map (Φ : PositiveTracePreservingMap H K) (A : PositiveTraceClass H) :
    ‖(map Φ A).1‖ = ‖A.1‖ := Φ.norm_map_of_nonneg A.1 A.2

end PositiveTraceClass

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- An integrable positive operator-valued density over a continuous classical
register. Two representatives agreeing almost everywhere describe the same state. -/
structure PositiveField where
  value : Ω → PositiveTraceClass H
  measurable : AEStronglyMeasurable value μ
  integrable : Integrable (fun x => (value x).1) μ

namespace PositiveField

variable {μ}

/-- Every integrable trace-class-valued function with positive fibres gives a
hybrid positive field. The positive-cone measurability is derived. -/
def ofIntegrable (f : Ω → TraceClass H) (hf : Integrable f μ)
    (hpos : ∀ x, 0 ≤ (f x).1) : PositiveField (H := H) μ where
  value := fun x => ⟨f x, hpos x⟩
  measurable := Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp hf.aestronglyMeasurable
  integrable := hf

/-- The integrated trace, equivalently the `L¹` norm of a positive density. -/
def mass (R : PositiveField (H := H) μ) : ℝ := ∫ x, ‖(R.value x).1‖ ∂μ

lemma mass_nonneg (R : PositiveField (H := H) μ) : 0 ≤ R.mass :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- The state after forgetting the classical register. -/
def quantumMarginal (R : PositiveField (H := H) μ) : TraceClass H :=
  ∫ x, (R.value x).1 ∂μ

lemma mass_eq_integral_trace (R : PositiveField (H := H) μ) :
    R.mass = ∫ x, (traceCLM (R.value x).1).re ∂μ := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    TraceClass.norm_eq_trace_re_of_nonneg (R.value x).1 (R.value x).2

lemma trace_quantumMarginal (R : PositiveField (H := H) μ) :
    (traceCLM R.quantumMarginal).re = R.mass := by
  rw [mass_eq_integral_trace, quantumMarginal,
    ← ContinuousLinearMap.integral_comp_comm _ R.integrable]
  exact (Complex.reCLM.integral_comp_comm
    (traceCLM.integrable_comp R.integrable)).symm

/-- The genuine hybrid trace distance before the conventional factor `1/2`. -/
def traceDistance (R S : PositiveField (H := H) μ) : ℝ :=
  ∫ x, ‖(R.value x).1 - (S.value x).1‖ ∂μ

lemma traceDistance_nonneg (R S : PositiveField (H := H) μ) : 0 ≤ R.traceDistance S :=
  integral_nonneg (fun _ => norm_nonneg _)

lemma traceDistance_comm (R S : PositiveField (H := H) μ) :
    R.traceDistance S = S.traceDistance R := by
  simp only [traceDistance, norm_sub_rev]

@[simp] lemma traceDistance_self (R : PositiveField (H := H) μ) : R.traceDistance R = 0 := by
  simp [traceDistance]

lemma traceDistance_triangle (R S T : PositiveField (H := H) μ) :
    R.traceDistance T ≤ R.traceDistance S + S.traceDistance T := by
  calc
    R.traceDistance T ≤ ∫ x, (‖(R.value x).1 - (S.value x).1‖ +
        ‖(S.value x).1 - (T.value x).1‖) ∂μ := by
      apply integral_mono (R.integrable.sub T.integrable).norm
        ((R.integrable.sub S.integrable).norm.add (S.integrable.sub T.integrable).norm)
      intro x
      simpa only [dist_eq_norm] using dist_triangle (R.value x).1 (S.value x).1 (T.value x).1
    _ = R.traceDistance S + S.traceDistance T :=
      integral_add (R.integrable.sub S.integrable).norm (S.integrable.sub T.integrable).norm

/-- A positive trace-preserving quantum map applied in every classical fibre. -/
def map (Φ : PositiveTracePreservingMap H K) (R : PositiveField (H := H) μ) :
    PositiveField (H := K) μ where
  value := fun x => PositiveTraceClass.map Φ (R.value x)
  measurable := (PositiveTraceClass.continuous_map Φ).comp_aestronglyMeasurable R.measurable
  integrable := Φ.toContinuousLinearMap.integrable_comp R.integrable

@[simp] lemma mass_map (Φ : PositiveTracePreservingMap H K) (R : PositiveField (H := H) μ) :
    (R.map Φ).mass = R.mass := by simp only [mass, map, PositiveTraceClass.norm_map]

/-- Hybrid trace distance contracts under every fibrewise positive TP map. -/
theorem traceDistance_map_le (Φ : PositiveTracePreservingMap H K)
    (R S : PositiveField (H := H) μ) :
    (R.map Φ).traceDistance (S.map Φ) ≤ R.traceDistance S := by
  apply integral_mono ((R.map Φ).integrable.sub (S.map Φ).integrable).norm
    (R.integrable.sub S.integrable).norm
  intro x
  exact Φ.norm_map_sub_le (R.value x).1 (S.value x).1 (R.value x).2 (S.value x).2

lemma quantumMarginal_map (Φ : PositiveTracePreservingMap H K)
    (R : PositiveField (H := H) μ) :
    (R.map Φ).quantumMarginal = Φ R.quantumMarginal := by
  exact Φ.toContinuousLinearMap.integral_comp_comm R.integrable

end PositiveField
end Cloning.Hybrid
