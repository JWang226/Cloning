import Cloning.HybridJensen
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Forgetting an arbitrary sigma-finite classical register increases quantum
root fidelity. In particular, the result applies directly to Lebesgue-density
hybrid Gaussian models, without replacing Lebesgue measure by a prior. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open MeasureTheory Filter Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.Hybrid.PositiveField
set_option backward.isDefEq.respectTransparency false
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restrict the classical register to a measurable region; the retained field
is allowed to have trace strictly below one. -/
def restrict (R : PositiveField (H := H) μ) (s : Set Ω) :
    PositiveField (H := H) (μ.restrict s) :=
  ofIntegrable (fun x => (R.value x).1) R.integrable.restrict (fun x => (R.value x).2)

lemma quantumMarginal_spanning_tendsto [SigmaFinite μ] (R : PositiveField (H := H) μ) :
    Tendsto (fun n => (R.restrict (spanningSets μ n)).quantumMarginal)
      atTop (𝓝 R.quantumMarginal) := by
  have h := tendsto_setIntegral_of_monotone (measurableSet_spanningSets μ)
    (monotone_spanningSets μ)
    (show IntegrableOn (fun x => (R.value x).1) (⋃ n, spanningSets μ n) μ by
      simpa only [iUnion_spanningSets, integrableOn_univ] using R.integrable)
  simpa only [iUnion_spanningSets, setIntegral_univ] using h

lemma rootFidelity_spanning_tendsto [SigmaFinite μ] (R S : PositiveField (H := H) μ) :
    Tendsto (fun n => (R.restrict (spanningSets μ n)).rootFidelity
      (S.restrict (spanningSets μ n))) atTop (𝓝 (R.rootFidelity S)) := by
  have h := tendsto_setIntegral_of_monotone (measurableSet_spanningSets μ)
    (monotone_spanningSets μ)
    (show IntegrableOn (fun x => PositiveTraceClass.rootFidelity (R.value x) (S.value x))
        (⋃ n, spanningSets μ n) μ by
      simpa only [iUnion_spanningSets, integrableOn_univ] using R.integrable_rootFidelity S)
  simpa only [iUnion_spanningSets, setIntegral_univ] using h

/-- General Bochner-mixture concavity, valid on infinite sigma-finite measures.
Both arbitrary positive operator-valued densities may vary with the classical
register, and no commutativity or rank assumption occurs. -/
theorem rootFidelity_le_marginal_sigmaFinite [SigmaFinite μ]
    (R S : PositiveField (H := H) μ) :
    R.rootFidelity S ≤ fidelity R.quantumMarginal.1 S.quantumMarginal.1
      R.quantumMarginal_nonneg S.quantumMarginal_nonneg R.quantumMarginal.2 S.quantumMarginal.2 := by
  have hineq (n : ℕ) := by
    letI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using measure_spanningSets_lt_top μ n⟩
    exact rootFidelity_le_marginal_finite (R.restrict (spanningSets μ n))
      (S.restrict (spanningSets μ n))
  let A (n : ℕ) : PositiveTraceClass H :=
    ⟨(R.restrict (spanningSets μ n)).quantumMarginal,
      (R.restrict (spanningSets μ n)).quantumMarginal_nonneg⟩
  let B (n : ℕ) : PositiveTraceClass H :=
    ⟨(S.restrict (spanningSets μ n)).quantumMarginal,
      (S.restrict (spanningSets μ n)).quantumMarginal_nonneg⟩
  let A₀ : PositiveTraceClass H := ⟨R.quantumMarginal, R.quantumMarginal_nonneg⟩
  let B₀ : PositiveTraceClass H := ⟨S.quantumMarginal, S.quantumMarginal_nonneg⟩
  have hA : Tendsto A atTop (𝓝 A₀) := tendsto_subtype_rng.mpr R.quantumMarginal_spanning_tendsto
  have hB : Tendsto B atTop (𝓝 B₀) := tendsto_subtype_rng.mpr S.quantumMarginal_spanning_tendsto
  have hlim := PositiveTraceClass.continuous_rootFidelity.continuousAt.tendsto.comp
    (hA.prodMk_nhds hB)
  exact le_of_tendsto_of_tendsto (R.rootFidelity_spanning_tendsto S) hlim
    (Eventually.of_forall hineq)

/-- Direct operator-valued form of joint concavity under Bochner integration. -/
theorem integral_fidelity_le_fidelity_integral [SigmaFinite μ]
    (A B : Ω → TraceClass H) (hA : Integrable A μ) (hB : Integrable B μ)
    (hposA : ∀ x, 0 ≤ (A x).1) (hposB : ∀ x, 0 ≤ (B x).1) :
    (∫ x, fidelity (A x).1 (B x).1 (hposA x) (hposB x) (A x).2 (B x).2 ∂μ) ≤
      fidelity (∫ x, A x ∂μ).1 (∫ x, B x ∂μ).1
        (ofIntegrable A hA hposA).quantumMarginal_nonneg
        (ofIntegrable B hB hposB).quantumMarginal_nonneg
        (∫ x, A x ∂μ).2 (∫ x, B x ∂μ).2 :=
  rootFidelity_le_marginal_sigmaFinite (ofIntegrable A hA hposA) (ofIntegrable B hB hposB)

end Cloning.Hybrid.PositiveField
