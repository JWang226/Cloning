import Cloning.MixedChannelsFiniteInstrument
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Quantum-to-hybrid assembly from a genuine finite orthogonal decomposition.
Each summand may have its own Hilbert space and its own actual quantum channel.
The trace normalization of the instrument follows from the complete Hilbert sum.
-/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators Classical ENNReal
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]
  (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)

theorem hilbertSum_adjoint_eq_coordinate (i : ι) (x : H) :
    (V i).toContinuousLinearMap.adjoint x = hV.linearIsometryEquiv x i := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    ⟪V i y, x⟫_ℂ =
        ⟪hV.linearIsometryEquiv.symm (lp.single 2 i y),
          hV.linearIsometryEquiv.symm (hV.linearIsometryEquiv x)⟫_ℂ := by
      rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single,
        LinearIsometryEquiv.symm_apply_apply]
    _ = _ := by rw [LinearIsometryEquiv.inner_map_map, lp.inner_single_left]

def hilbertSumProjection (i : ι) : H →L[ℂ] H :=
  (V i).toContinuousLinearMap.comp (V i).toContinuousLinearMap.adjoint

include hV in
theorem hilbertSumProjection_complete : RectangularKrausComplete (hilbertSumProjection V) := by
  intro x
  have hs := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (hV.linearIsometryEquiv x)
  simpa only [hilbertSumProjection, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    hilbertSum_adjoint_eq_coordinate V hV, ENNReal.toReal_ofNat, Real.rpow_two,
    LinearIsometryEquiv.norm_map] using hs

theorem hilbertSum_compressed_trace (i : ι) (A : TraceClass H) :
    traceCLM (conjugationLinearMap (V i).toContinuousLinearMap.adjoint A) =
      traceCLM (conjugationLinearMap (hilbertSumProjection V i) A) := by
  rw [← conjugationLinearMap_isometry_trace (V i)
    (conjugationLinearMap (V i).toContinuousLinearMap.adjoint A)]
  congr 1
  apply Subtype.ext
  ext x
  simp only [conjugationLinearMap_coe, operatorConjugation_apply,
    hilbertSumProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]

include hV in
theorem hilbertSum_compressed_trace_sum (A : TraceClass H) :
    (∑ i, traceCLM (conjugationLinearMap (V i).toContinuousLinearMap.adjoint A)) =
      traceCLM A := by
  simp_rw [hilbertSum_compressed_trace V]
  simpa only [rectangularKrausLinearMap_apply, tsum_fintype, map_sum] using
    rectangularKrausLinearMap_trace (hilbertSumProjection V)
      (hilbertSumProjection_complete V hV) A

variable (Φ : ∀ i, QuantumChannel (E i) K)
    (g : ι → Ω → ℝ) (hg : ∀ i, Integrable (g i) μ)
    (hg0 : ∀ i y, 0 ≤ g i y) (hprob : ∀ i, ∫ y, g i y ∂μ = 1)

def sectorInstrumentPart (i : ι) : TraceClass H →ₗ[ℂ] TraceClass K :=
  (Φ i).toLinearMap.comp (conjugationLinearMap (V i).toContinuousLinearMap.adjoint)

theorem sectorInstrumentPart_completelyPositive (i : ι) :
    IsCompletelyPositive (sectorInstrumentPart V Φ i) := by
  intro n A hA
  exact (Φ i).completelyPositive n _
    (conjugationLinearMap_completelyPositive (V i).toContinuousLinearMap.adjoint n A hA)

include hV in
theorem sectorInstrumentPart_trace_sum (A : TraceClass H) :
    (∑ i, traceCLM (sectorInstrumentPart V Φ i A)) = traceCLM A := by
  calc
    _ = ∑ i, traceCLM (conjugationLinearMap (V i).toContinuousLinearMap.adjoint A) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Φ i).toPositiveTracePreservingMap.trace_preserving _
    _ = _ := hilbertSum_compressed_trace_sum V hV A

/-- A complete physical orthogonal decomposition and genuine sector channels
produce the forward mixed channel, without a separate normalization premise. -/
def QuantumToHybrid.ofHilbertSum : QuantumToHybrid H K μ :=
  QuantumToHybrid.finiteInstrument (sectorInstrumentPart V Φ)
    (sectorInstrumentPart_completelyPositive V Φ) (sectorInstrumentPart_trace_sum V hV Φ)
    g hg hg0 hprob

@[simp] theorem QuantumToHybrid.ofHilbertSum_apply (A : TraceClass H) :
    (QuantumToHybrid.ofHilbertSum V hV Φ g hg hg0 hprob).map A =
      ∑ i, prepareL1 (g i) (hg i)
        ((Φ i).toLinearMap (conjugationLinearMap (V i).toContinuousLinearMap.adjoint A)) :=
  finiteInstrumentLinearMap_apply _ _ _ _

end Cloning.Hybrid
