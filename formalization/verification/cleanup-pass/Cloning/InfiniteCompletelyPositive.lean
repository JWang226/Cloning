import Cloning.InfiniteTraceClassCutoff
import Cloning.InfiniteTraceClassDecomposition

/-!
# Complete positivity of actual trace-class maps

Finite-ancilla positivity is expressed directly by the quadratic form of a
finite matrix of bounded trace-class operators. This definition tests arbitrary
vectors in the finite Hilbert direct sum, including entangled ones.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace BigOperators

variable {H K J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
variable {ι : Type*} [Fintype ι]

/-- Positivity of the operator on the finite Hilbert direct sum. -/
def BlockPositive (A : ι → ι → TraceClass H) : Prop :=
  ∀ x : ι → H, 0 ≤ ∑ i, ∑ j, ⟪x i, (A i j).1 (x j)⟫_ℂ

/-- Complete positivity at every finite ancilla dimension. -/
def IsCompletelyPositive (Φ : TraceClass H →ₗ[ℂ] TraceClass K) : Prop :=
  ∀ n : ℕ, ∀ A : Fin n → Fin n → TraceClass H,
    BlockPositive A → BlockPositive (fun i j => Φ (A i j))

omit [CompleteSpace H] in
theorem nonneg_of_inner_nonneg (T : H →L[ℂ] H)
    (h : ∀ x, 0 ≤ ⟪x, T x⟫_ℂ) : 0 ≤ T := by
  apply T.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
  intro x
  have hx := Complex.nonneg_iff.mp (h x)
  have heq : ⟪T x, x⟫_ℂ = star ⟪x, T x⟫_ℂ := (inner_conj_symm _ _).symm
  rw [heq]
  constructor
  · apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re, Complex.ofReal_re]
      rfl
    · simp only [Complex.star_def, Complex.conj_im, Complex.ofReal_im, ← hx.2, neg_zero]
  · simpa only [Complex.star_def, Complex.conj_re] using hx.1

theorem BlockPositive.scalarCompression {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (c : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, (star (c i) * c j) • A i j : TraceClass H).1 := by
  apply nonneg_of_inner_nonneg
  intro y
  have h := hA (fun i => c i • y)
  convert h using 1
  change ⟪y, inclusionCLM (∑ i, ∑ j, (star (c i) * c j) • A i j) y⟫_ℂ = _
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right,
    inner_smul_left, inclusionCLM_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [starRingEnd_apply]
  ring

theorem BlockPositive.traceMatrix {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * c j * traceCLM (A i j) := by
  let T : TraceClass H := ∑ i, ∑ j, (star (c i) * c j) • A i j
  have hp := hA.scalarCompression c
  have ht := trace_eq_traceNorm_of_nonneg hp T.2
  have h : 0 ≤ traceCLM T := by
    change 0 ≤ trace T.1 T.2
    rw [ht]
    exact_mod_cast traceNorm_nonneg T.1 T.2
  simpa only [T, map_sum, map_smul, smul_eq_mul] using h

theorem BlockPositive.sandwich {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (P : H →L[ℂ] H) (hP : IsSelfAdjoint P) :
    BlockPositive (fun i j => sandwichCLM P P (A i j)) := by
  intro x
  convert hA (fun i => P (x i)) using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, P ((A i j).1 (P (x j)))⟫_ℂ = _
  exact (hP.isSymmetric (x i) ((A i j).1 (P (x j)))).symm

theorem BlockPositive.replacePure {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (z : K) :
    BlockPositive (fun i j => traceCLM (A i j) • vectorProjector z) := by
  intro x
  convert hA.traceMatrix (fun i => ⟪z, x i⟫_ℂ) using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, (traceCLM (A i j) • InnerProductSpace.rankOne ℂ z z) (x j)⟫_ℂ = _
  simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right, ← inner_conj_symm (x i) z]
  simp only [starRingEnd_apply]
  ring

/-- A fixed finite block test is continuous in the replacement operator. -/
def replacementExpectation (C : ι → ι → ℂ) (x : ι → K) : TraceClass K →L[ℂ] ℂ :=
  ∑ i, ∑ j, C i j •
    ((innerSL ℂ (x i)).comp ((ContinuousLinearMap.apply ℂ K (x j)).comp inclusionCLM))

theorem replacementExpectation_apply (C : ι → ι → ℂ) (x : ι → K) (σ : TraceClass K) :
    replacementExpectation C x σ = ∑ i, ∑ j, C i j * ⟪x i, σ.1 (x j)⟫_ℂ := by
  simp [replacementExpectation, inclusionCLM_apply]

theorem BlockPositive.replace {A : ι → ι → TraceClass H}
    (hA : BlockPositive A) (σ : TraceClass K) (hσ : 0 ≤ σ.1) :
    BlockPositive (fun i j => traceCLM (A i j) • σ) := by
  intro x
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  let E := replacementExpectation (fun i j => traceCLM (A i j)) x
  have hs := (positive_rankOne_series hσ σ.2 b).mapL E
  have hnonneg : ∀ k : w, 0 ≤ E (vectorProjector (CFC.sqrt σ.1 (b k))) := by
    intro k
    have h := hA.replacePure (CFC.sqrt σ.1 (b k)) x
    change 0 ≤ replacementExpectation (fun i j => traceCLM (A i j)) x _
    rw [replacementExpectation_apply]
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change _ = ⟪x i, (traceCLM (A i j) •
      (vectorProjector (CFC.sqrt σ.1 (b k))).1) (x j)⟫_ℂ
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  have hsum : 0 ≤ E (TraceClass.ofOperator σ.1 σ.2) := by
    rw [← hs.tsum_eq]
    exact tsum_nonneg hnonneg
  change 0 ≤ E σ at hsum
  rw [replacementExpectation_apply] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, (traceCLM (A i j) • σ.1) (x j)⟫_ℂ = _
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

theorem projectionReplacement_completelyPositive (P : H →L[ℂ] H)
    (hP : IsStarProjection P) (σ : DensityState H) :
    IsCompletelyPositive (projectionReplacement P hP σ).toLinearMap := by
  intro n A hA x
  have hleft := hA.sandwich P hP.isSelfAdjoint x
  have hright := (hA.sandwich (1 - P) hP.one_sub.isSelfAdjoint).replace
    (TraceClass.ofOperator σ.op σ.traceClass) σ.positive x
  convert add_nonneg hleft hright using 1
  simp only [projectionReplacement_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ⟪x i, ((sandwichCLM P P (A i j)).1 +
      traceCLM (sandwichCLM (1 - P) (1 - P) (A i j)) • σ.op) (x j)⟫_ℂ = _
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  rfl

/-- A genuine infinite-dimensional CPTP map on the trace-class Banach space. -/
structure QuantumChannel (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    extends PositiveTracePreservingMap H K where
  completelyPositive : IsCompletelyPositive toLinearMap

def QuantumChannel.projectionReplacement (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (σ : DensityState H) : QuantumChannel H H where
  toPositiveTracePreservingMap := Cloning.InfiniteTraceClass.projectionReplacement P hP σ
  completelyPositive := projectionReplacement_completelyPositive P hP σ

def QuantumChannel.id : QuantumChannel H H where
  toPositiveTracePreservingMap := PositiveTracePreservingMap.id
  completelyPositive := fun _ _ hA => hA

def QuantumChannel.comp (Ψ : QuantumChannel K J) (Φ : QuantumChannel H K) :
    QuantumChannel H J where
  toPositiveTracePreservingMap := Ψ.toPositiveTracePreservingMap.comp Φ.toPositiveTracePreservingMap
  completelyPositive := fun n A hA => Ψ.completelyPositive n _ (Φ.completelyPositive n A hA)

end
end Cloning.InfiniteTraceClass
