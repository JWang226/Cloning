import Cloning.HybridChannelAveraging
import Cloning.HybridL1Fidelity
import Cloning.InfiniteChannelFidelity

/-! Genuine channels between quantum trace class and classical–quantum L¹.
The finite-ancilla positivity and trace laws concern every input. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false

variable {Ω H K J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- A channel from quantum trace class into the actual operator-valued L¹ space. -/
structure QuantumToHybrid (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (μ : Measure Ω) where
  map : TraceClass H →L[ℂ] Lp (TraceClass K) 1 μ
  completelyPositive : ∀ n (A : Fin n → Fin n → TraceClass H),
    BlockPositive A → L1BlockPositive (fun i j => map (A i j))
  tracePreserving : ∀ A, integratedTrace (map A) = traceCLM A

/-- A channel from classical–quantum L¹ into quantum trace class. -/
structure HybridToQuantum (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (μ : Measure Ω) where
  map : Lp (TraceClass H) 1 μ →L[ℂ] TraceClass K
  completelyPositive : ∀ n (A : Fin n → Fin n → Lp (TraceClass H) 1 μ),
    L1BlockPositive A → BlockPositive (fun i j => map (A i j))
  tracePreserving : ∀ A, traceCLM (map A) = integratedTrace A

theorem QuantumToHybrid.map_nonneg (T : QuantumToHybrid H K μ)
    (A : TraceClass H) (hA : 0 ≤ A.1) : ∀ᵐ y ∂μ, 0 ≤ (T.map A y).1 := by
  have hi : BlockPositive (fun _ _ : Fin 1 => A) := by
    intro v
    simpa only [Fin.sum_univ_one] using
      (A.1.nonneg_iff_isPositive.mp hA).inner_nonneg_right (v 0)
  filter_upwards [T.completelyPositive 1 (fun _ _ => A) hi] with y hy
  apply nonneg_of_inner_nonneg
  intro v
  simpa only [Fin.sum_univ_one] using hy (fun _ => v)

theorem HybridToQuantum.map_nonneg (S : HybridToQuantum H K μ)
    (A : Lp (TraceClass H) 1 μ) (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    0 ≤ (S.map A).1 := by
  have hi : L1BlockPositive (fun _ _ : Fin 1 => A) := by
    filter_upwards [hA] with y hy
    intro v
    simpa only [Fin.sum_univ_one] using
      ((A y).1.nonneg_iff_isPositive.mp hy).inner_nonneg_right (v 0)
  apply nonneg_of_inner_nonneg
  intro v
  simpa only [Fin.sum_univ_one] using
    S.completelyPositive 1 (fun _ _ => A) hi (fun _ => v)

def QuantumToHybrid.mapPositive (T : QuantumToHybrid H K μ)
    (A : PositiveTraceClass H) : PositiveL1 K μ :=
  ⟨T.map A.1, T.map_nonneg A.1 A.2⟩

def HybridToQuantum.mapPositive (S : HybridToQuantum H K μ)
    (A : PositiveL1 H μ) : PositiveTraceClass K :=
  ⟨S.map A.1, S.map_nonneg A.1 A.2⟩

theorem QuantumToHybrid.norm_map_of_nonneg (T : QuantumToHybrid H K μ)
    (A : TraceClass H) (hA : 0 ≤ A.1) : ‖T.map A‖ = ‖A‖ := by
  rw [norm_L1_eq_trace_re _ (T.map_nonneg A hA), ← integratedTrace_apply,
    T.tracePreserving, TraceClass.norm_eq_trace_re_of_nonneg A hA]
  rfl

theorem HybridToQuantum.norm_map_of_nonneg (S : HybridToQuantum H K μ)
    (A : Lp (TraceClass H) 1 μ) (hA : ∀ᵐ y ∂μ, 0 ≤ (A y).1) :
    ‖S.map A‖ = ‖A‖ := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (S.map_nonneg A hA),
    norm_L1_eq_trace_re A hA]
  exact congrArg Complex.re ((S.tracePreserving A).trans (integratedTrace_apply A))

/-- Exact trace-norm contraction on the self-adjoint quantum part. -/
theorem QuantumToHybrid.norm_map_le_of_isSelfAdjoint (T : QuantumToHybrid H K μ)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) : ‖T.map A‖ ≤ ‖A‖ := by
  calc
    ‖T.map A‖ = ‖T.map (TraceClass.positivePart A hA) -
        T.map (TraceClass.negativePart A hA)‖ := by
      rw [← map_sub, TraceClass.positivePart_sub_negativePart A hA]
    _ ≤ ‖T.map (TraceClass.positivePart A hA)‖ +
        ‖T.map (TraceClass.negativePart A hA)‖ := norm_sub_le _ _
    _ = ‖TraceClass.positivePart A hA‖ + ‖TraceClass.negativePart A hA‖ := by
      rw [T.norm_map_of_nonneg _ (TraceClass.positivePart_nonneg A hA),
        T.norm_map_of_nonneg _ (TraceClass.negativePart_nonneg A hA)]
    _ = ‖A‖ := TraceClass.norm_positivePart_add_norm_negativePart A hA

theorem QuantumToHybrid.norm_map_sub_le (T : QuantumToHybrid H K μ)
    (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    ‖T.map A - T.map B‖ ≤ ‖A - B‖ := by
  rw [← map_sub]
  exact T.norm_map_le_of_isSelfAdjoint _
    ((IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB))

theorem QuantumToHybrid.norm_le_two (T : QuantumToHybrid H K μ) (A : TraceClass H) :
    ‖T.map A‖ ≤ 2 * ‖A‖ := by
  simpa only [mul_one] using norm_map_two_mul_of_positive_bound T.map.toLinearMap
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun B hB => le_of_eq ((T.norm_map_of_nonneg B hB).trans (one_mul ‖B‖).symm)) A

/-- Precomposition with an arbitrary physical quantum competitor. -/
def QuantumToHybrid.compQuantum (T : QuantumToHybrid K J μ) (M : QuantumChannel H K) :
    QuantumToHybrid H J μ where
  map := T.map.comp M.toPositiveTracePreservingMap.toContinuousLinearMap
  completelyPositive := fun n A hA =>
    T.completelyPositive n _ (M.completelyPositive n A hA)
  tracePreserving := fun A => (T.tracePreserving (M.toLinearMap A)).trans
    (M.toPositiveTracePreservingMap.trace_preserving A)

/-- The mixed composition acts on all hybrid inputs and is an actual hybrid channel. -/
def QuantumToHybrid.compHybridToQuantum (T : QuantumToHybrid K J μ)
    (S : HybridToQuantum H K μ) : Channel H J μ where
  map := T.map.comp S.map
  completelyPositive := fun n A hA => T.completelyPositive n _ (S.completelyPositive n A hA)
  tracePreserving := fun A => by
    rw [← integratedTrace_apply, ← integratedTrace_apply]
    exact (T.tracePreserving (S.map A)).trans (S.tracePreserving A)

/-- Composition in the other direction is a genuine quantum CPTP map. -/
def HybridToQuantum.compQuantumToHybrid (S : HybridToQuantum K J μ)
    (T : QuantumToHybrid H K μ) : QuantumChannel H J where
  toLinearMap := (S.map.comp T.map).toLinearMap
  map_nonneg := fun A hA => S.map_nonneg _ (T.map_nonneg A hA)
  trace_preserving := fun A => (S.tracePreserving (T.map A)).trans (T.tracePreserving A)
  completelyPositive := fun n A hA => S.completelyPositive n _ (T.completelyPositive n A hA)

@[simp] theorem QuantumToHybrid.compQuantum_apply (T : QuantumToHybrid K J μ)
    (M : QuantumChannel H K) (A : TraceClass H) :
    (T.compQuantum M).map A = T.map (M.toLinearMap A) := rfl

@[simp] theorem QuantumToHybrid.compHybridToQuantum_apply (T : QuantumToHybrid K J μ)
    (S : HybridToQuantum H K μ) (A : Lp (TraceClass H) 1 μ) :
    (T.compHybridToQuantum S).map A = T.map (S.map A) := rfl

@[simp] theorem HybridToQuantum.compQuantumToHybrid_apply (S : HybridToQuantum K J μ)
    (T : QuantumToHybrid H K μ) (A : TraceClass H) :
    (S.compQuantumToHybrid T).toLinearMap A = S.map (T.map A) := rfl

end Cloning.Hybrid
