import Cloning.MixedChannelsSectorInstrument
import Cloning.MixedChannelsFiniteSelector
import Cloning.HeisenbergDualResidual

/-! Finite stochastic instruments on the actual trace-class spaces. -/
noncomputable section
open scoped BigOperators ComplexOrder InnerProductSpace Classical
namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι]

theorem IsCompletelyPositive.fintype_sum
    (I : ι → TraceClass H →ₗ[ℂ] TraceClass K) (hI : ∀ i, IsCompletelyPositive (I i)) :
    IsCompletelyPositive (∑ i, I i) := by
  intro n A hA
  simpa only [LinearMap.sum_apply] using
    Cloning.Hybrid.finite_blockPositive_sum (fun i a b ↦ I i (A a b)) (fun i ↦ hI i n A hA)

/-- A finite complete instrument is a genuine quantum channel on all complex
trace-class inputs. -/
def QuantumChannel.ofFiniteInstrument (I : ι → TraceClass H →ₗ[ℂ] TraceClass K)
    (hI : ∀ i, IsCompletelyPositive (I i))
    (htrace : ∀ A, ∑ i, traceCLM (I i A) = traceCLM A) : QuantumChannel H K where
  toLinearMap := ∑ i, I i
  map_nonneg := (IsCompletelyPositive.fintype_sum I hI).map_nonneg
  trace_preserving A := by
    change traceCLM ((∑ i, I i) A) = traceCLM A
    simpa only [LinearMap.sum_apply, map_sum] using htrace A
  completelyPositive := IsCompletelyPositive.fintype_sum I hI

@[simp] theorem QuantumChannel.ofFiniteInstrument_apply
    (I : ι → TraceClass H →ₗ[ℂ] TraceClass K)
    (hI : ∀ i, IsCompletelyPositive (I i))
    (htrace : ∀ A, ∑ i, traceCLM (I i A) = traceCLM A) (A : TraceClass H) :
    (QuantumChannel.ofFiniteInstrument I hI htrace).toLinearMap A = ∑ i, I i A :=
  LinearMap.sum_apply _ _ _

/-- A finite classical probability mixture of genuine channels. -/
def QuantumChannel.finiteMixture (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (Φ : ι → QuantumChannel H K) : QuantumChannel H K :=
  QuantumChannel.ofFiniteInstrument (fun i ↦ (q i : ℂ) • (Φ i).toLinearMap)
    (fun i ↦ (Φ i).completelyPositive.real_smul (hq i)) (by
      intro A
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      have ht (i : ι) : traceCLM ((Φ i).toLinearMap A) = traceCLM A :=
        (Φ i).toPositiveTracePreservingMap.trace_preserving A
      simp_rw [ht]
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hs, Complex.ofReal_one, one_mul])

@[simp] theorem QuantumChannel.finiteMixture_apply (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hs : ∑ i, q i = 1) (Φ : ι → QuantumChannel H K) (A : TraceClass H) :
    (QuantumChannel.finiteMixture q hq hs Φ).toLinearMap A =
      ∑ i, (q i : ℂ) • (Φ i).toLinearMap A := by
  simp [QuantumChannel.finiteMixture]

variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]

/-- Measure the complete physical orthogonal sector decomposition and apply
a genuine channel to each measured sector. -/
def QuantumChannel.ofHilbertSum (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (Φ : ∀ i, QuantumChannel (E i) K) : QuantumChannel H K :=
  QuantumChannel.ofFiniteInstrument (Cloning.Hybrid.sectorInstrumentPart V Φ)
    (Cloning.Hybrid.sectorInstrumentPart_completelyPositive V Φ)
    (Cloning.Hybrid.sectorInstrumentPart_trace_sum V hV Φ)

@[simp] theorem QuantumChannel.ofHilbertSum_apply
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (Φ : ∀ i, QuantumChannel (E i) K) (A : TraceClass H) :
    (QuantumChannel.ofHilbertSum V hV Φ).toLinearMap A =
      ∑ i, (Φ i).toLinearMap (conjugationLinearMap (V i).toContinuousLinearMap.adjoint A) := by
  simp [QuantumChannel.ofHilbertSum, Cloning.Hybrid.sectorInstrumentPart]

end Cloning.InfiniteTraceClass
