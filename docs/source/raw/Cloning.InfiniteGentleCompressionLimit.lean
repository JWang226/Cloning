import Cloning.InfiniteGentleCompression
import Cloning.InfiniteFiniteCorner

/-! Positive unit-trace operators converge in actual trace norm once their
matrix coefficients converge to those of a positive unit-trace limit. -/
noncomputable section
open scoped BigOperators ComplexOrder InnerProductSpace Topology Classical
open Filter
namespace Cloning.InfiniteTraceClass
open Cloning.InfiniteFiniteCorner
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {α ι : Type*} {l : Filter α}

theorem matrixLift_basis_eq_sandwich (b : HilbertBasis ι ℂ H) (s : Finset ι)
    (A : TraceClass H) :
    matrixLift (fun i : s ↦ b i) (matrixOf (fun i : s ↦ b i) A.1) =
      sandwichCLM (basisProjection b s) (basisProjection b s) A := by
  apply Subtype.ext
  exact ofMatrix_matrixOf_basis b s A.1

theorem finite_corner_tendsto_of_coefficients (b : HilbertBasis ι ℂ H)
    (A : α → TraceClass H) (B : TraceClass H)
    (hcoeff : ∀ i j, Tendsto (fun n ↦ ⟪b i, (A n).1 (b j)⟫_ℂ) l (𝓝 ⟪b i, B.1 (b j)⟫_ℂ))
    (s : Finset ι) :
    Tendsto (fun n ↦ sandwichCLM (basisProjection b s) (basisProjection b s) (A n)) l
      (𝓝 (sandwichCLM (basisProjection b s) (basisProjection b s) B)) := by
  simp_rw [← matrixLift_basis_eq_sandwich, matrixLift, matrixOf]
  apply tendsto_finset_sum
  intro i hi
  apply tendsto_finset_sum
  intro j hj
  exact (hcoeff i.val j.val).smul_const _

/-- Finite-corner convergence and exact total mass exclude escape of positive
mass to infinity. The proof quantitatively controls both off-diagonal tails. -/
theorem tendsto_of_positive_unit_corners (b : HilbertBasis ι ℂ H)
    (A : α → TraceClass H) (B : TraceClass H)
    (hA : ∀ n, 0 ≤ (A n).1) (hB : 0 ≤ B.1)
    (hAn : ∀ n, ‖A n‖ = 1) (hBn : ‖B‖ = 1)
    (hcorner : ∀ s : Finset ι,
      Tendsto (fun n ↦ sandwichCLM (basisProjection b s) (basisProjection b s) (A n)) l
        (𝓝 (sandwichCLM (basisProjection b s) (basisProjection b s) B))) :
    Tendsto A l (𝓝 B) := by
  let C (s : Finset ι) (T : TraceClass H) := sandwichCLM (basisProjection b s) (basisProjection b s) T
  have hBC : Tendsto (fun s : Finset ι ↦ C s B) atTop (𝓝 B) :=
    sandwich_tendsto_of_strong_projections _ (basisProjection_isStarProjection b)
      (basisProjection_tendsto b) B hB
  have hmass : Tendsto (fun s : Finset ι ↦ 1 - ‖C s B‖) atTop (𝓝 0) := by
    simpa only [hBn, sub_self] using hBC.norm.const_sub 1
  have hbound : Tendsto (fun s : Finset ι ↦
      2 * Real.sqrt (1-‖C s B‖) + ‖C s B-B‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, Real.sqrt_zero, mul_zero, zero_add] using
      ((Real.continuous_sqrt.continuousAt.tendsto.comp hmass).const_mul 2).add
        (hBC.sub_const B).norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := (hbound.eventually (gt_mem_nhds hε)).exists
  have hc : Tendsto (fun n ↦ C s (A n)) l (𝓝 (C s B)) := hcorner s
  have hn : Tendsto (fun n ↦ 2 * Real.sqrt (1-‖C s (A n)‖) +
      ‖C s (A n)-C s B‖ + ‖C s B-B‖) l
      (𝓝 (2 * Real.sqrt (1-‖C s B‖) + ‖C s B-B‖)) := by
    have hroot := (Real.continuous_sqrt.continuousAt.tendsto.comp (hc.norm.const_sub 1)).const_mul 2
    simpa only [sub_self, norm_zero, add_zero] using
      (hroot.add (hc.sub_const (C s B)).norm).add_const ‖C s B-B‖
  filter_upwards [hn.eventually (gt_mem_nhds hs)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt _ hn
  have hgentle := gentle_compression_unit (basisProjection_isStarProjection b s) (A n) (hA n) (hAn n)
  have htri := norm_sub_le_norm_sub_add_norm_sub (A n) (C s (A n)) B
  have htri' := norm_sub_le_norm_sub_add_norm_sub (C s (A n)) (C s B) B
  change ‖A n - C s (A n)‖ ≤ _ at hgentle
  linarith

/-- Quantum Scheffé convergence from actual Hilbert-basis matrix entries.
Positivity and total mass are verified properties of the operators, with no
finite-rank, tail or trace-norm approximation premise. -/
theorem tendsto_of_positive_unit_coefficients (b : HilbertBasis ι ℂ H)
    (A : α → TraceClass H) (B : TraceClass H)
    (hA : ∀ n, 0 ≤ (A n).1) (hB : 0 ≤ B.1)
    (hAn : ∀ n, ‖A n‖ = 1) (hBn : ‖B‖ = 1)
    (hcoeff : ∀ i j, Tendsto (fun n ↦ ⟪b i, (A n).1 (b j)⟫_ℂ) l (𝓝 ⟪b i, B.1 (b j)⟫_ℂ)) :
    Tendsto A l (𝓝 B) :=
  tendsto_of_positive_unit_corners b A B hA hB hAn hBn
    (finite_corner_tendsto_of_coefficients b A B hcoeff)

end Cloning.InfiniteTraceClass
