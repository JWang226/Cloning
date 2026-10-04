import Cloning.HybridWeightedTrace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Convex.Integral

/-! The almost-everywhere block-positive cone in the actual L1 Banach space
is closed and convex. Thus Bochner averages preserve complete positivity. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open MeasureTheory Filter Cloning.InfiniteTraceClass
namespace Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem isClosed_Lp_ae_mem {E : Type*} [NormedAddCommGroup E]
    {S : Set E} (hS : IsClosed S) : IsClosed {f : Lp E 1 μ | ∀ᵐ y ∂μ, f y ∈ S} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, _, he⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hm : ∀ᵐ y ∂μ, ∀ n : ℕ, f (ns n) y ∈ S := ae_all_iff.mpr fun n => hf (ns n)
  filter_upwards [he, hm] with y hy hm
  exact hS.mem_of_tendsto hy (Eventually.of_forall hm)

theorem coeFn_Lp_finset_sum {I E : Type*} [NormedAddCommGroup E]
    (t : Finset I) (A : I → Lp E 1 μ) :
    ((∑ i ∈ t, A i : Lp E 1 μ) : Ω → E) =ᵐ[μ] fun y => ∑ i ∈ t, A i y := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero E 1 μ)
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (A i) (∑ j ∈ t, A j), ih] with y hy hs
    simpa only [Pi.add_apply, hs] using hy

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Assemble finitely many L1 coordinates into the actual L1 of the product. -/
def assembleL1 : (I → Lp E 1 μ) →L[ℂ] Lp (I → E) 1 μ :=
  ∑ i, ((ContinuousLinearMap.single ℂ (fun _ : I => E) i).compLpL 1 μ).comp
    (ContinuousLinearMap.proj i)

theorem assembleL1_ae (A : I → Lp E 1 μ) :
    assembleL1 A =ᵐ[μ] fun y i => A i y := by
  have he : ∀ᵐ y ∂μ, ∀ i : I,
      ((ContinuousLinearMap.single ℂ (fun _ : I => E) i).compLpL 1 μ (A i)) y =
        Pi.single i (A i y) :=
    ae_all_iff.mpr fun i => (ContinuousLinearMap.single ℂ (fun _ : I => E) i).coeFn_compLpL (A i)
  simp only [assembleL1, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  filter_upwards [coeFn_Lp_finset_sum Finset.univ
    (fun i => (ContinuousLinearMap.single ℂ (fun _ : I => E) i).compLpL 1 μ (A i)), he] with y hy he
  rw [hy]
  simp only [he]
  ext i
  simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- Positivity of a finite matrix of L1 quantum densities. -/
def L1BlockPositive (A : Fin n → Fin n → Lp (TraceClass H) 1 μ) : Prop :=
  ∀ᵐ y ∂μ, BlockPositive (fun i j => A i j y)

theorem isClosed_flatBlockPositive :
    IsClosed {A : (Fin n × Fin n) → TraceClass H | BlockPositive (fun i j => A (i, j))} := by
  simp only [BlockPositive, Set.setOf_forall]
  apply isClosed_iInter
  intro v
  have hc : Continuous (fun A : (Fin n × Fin n) → TraceClass H =>
      ∑ i, ∑ j, ⟪v i, (A (i, j)).1 (v j)⟫_ℂ) := by
    apply continuous_finset_sum _
    intro i _
    apply continuous_finset_sum _
    intro j _
    exact (traceClassMatrixCoefficient (v i) (v j)).continuous.comp (continuous_apply (i, j))
  exact isClosed_le continuous_const hc

theorem isClosed_L1BlockPositive :
    IsClosed {A : Fin n → Fin n → Lp (TraceClass H) 1 μ | L1BlockPositive A} := by
  have hc : Continuous (fun A : Fin n → Fin n → Lp (TraceClass H) 1 μ =>
      assembleL1 (fun ij : Fin n × Fin n => A ij.1 ij.2)) :=
    assembleL1.continuous.comp (continuous_pi fun ij =>
      (continuous_apply ij.2).comp (continuous_apply ij.1))
  have hs := (isClosed_Lp_ae_mem (μ := μ) (isClosed_flatBlockPositive (H := H) (n := n))).preimage hc
  convert hs using 1
  ext A
  change (∀ᵐ y ∂μ, BlockPositive (fun i j => A i j y)) ↔
    (∀ᵐ y ∂μ, BlockPositive (fun i j => assembleL1 (fun ij : Fin n × Fin n => A ij.1 ij.2) y (i, j)))
  apply eventually_congr
  filter_upwards [assembleL1_ae (fun ij : Fin n × Fin n => A ij.1 ij.2)] with y hy
  rw [hy]

theorem convex_L1BlockPositive :
    Convex ℝ {A : Fin n → Fin n → Lp (TraceClass H) 1 μ | L1BlockPositive A} := by
  intro A hA B hB a b ha hb _
  have he : ∀ᵐ y ∂μ, ∀ i j : Fin n,
      (a • A i j + b • B i j) y = a • A i j y + b • B i j y := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_add (a • A i j) (b • B i j),
      Lp.coeFn_smul a (A i j), Lp.coeFn_smul b (B i j)] with y hadd hsmulA hsmulB
    simp only [hadd, Pi.add_apply, hsmulA, hsmulB, Pi.smul_apply]
  filter_upwards [hA, hB, he] with y hAy hBy hy
  intro v
  change 0 ≤ ∑ i, ∑ j, ⟪v i, ((a • A i j + b • B i j) y).1 (v j)⟫_ℂ
  simp only [hy]
  change 0 ≤ ∑ i, ∑ j, ⟪v i, (a • (A i j y).1 + b • (B i j y).1) (v j)⟫_ℂ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right_eq_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  exact add_nonneg (smul_nonneg ha (hAy v)) (smul_nonneg hb (hBy v))

/-- Bochner integration over any probability measure preserves the full
finite block-positive cone in operator-valued L1. -/
theorem L1BlockPositive_integral {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    [IsProbabilityMeasure ν] {A : Ξ → Fin n → Fin n → Lp (TraceClass H) 1 μ}
    (hA : Integrable A ν) (hp : ∀ᵐ ξ ∂ν, L1BlockPositive (A ξ)) :
    L1BlockPositive (∫ ξ, A ξ ∂ν) :=
  convex_L1BlockPositive.integral_mem isClosed_L1BlockPositive hp hA

end Cloning.Hybrid
