import Cloning.InfiniteFidelityHilbertSum
import Cloning.BlockFidelity

/-! Exact physical block factorization with a quantitative cost for deleting
positive mass. The states live in the actual Hilbert summands. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical
namespace Cloning.InfiniteFidelityHilbertSum
open Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_norm_eq_trace (A : PositiveTraceClass H) :
    ‖A.1‖ = (traceCLM A.1).re := TraceClass.norm_eq_trace_re_of_nonneg A.1 A.2

theorem norm_positive_sub (A B : PositiveTraceClass H) (h : B.1.1 ≤ A.1.1) :
    ‖A.1-B.1‖ = ‖A.1‖-‖B.1‖ := by
  have hp : 0 ≤ (A.1-B.1).1 := by
    change 0 ≤ A.1.1-B.1.1
    exact sub_nonneg.mpr h
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ hp, positive_norm_eq_trace A, positive_norm_eq_trace B]
  change (traceCLM (A.1-B.1)).re = _
  rw [map_sub, Complex.sub_re]

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]

theorem norm_orthogonalSum (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (A : ∀ i, PositiveTraceClass (E i)) : ‖(orthogonalSum V A).1‖ = ∑ i, ‖(A i).1‖ := by
  rw [positive_norm_eq_trace, orthogonalSum_val, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have ht := (QuantumChannel.ofIsometry (V i)).trace_preserving (A i).1
  change traceCLM (conjugationLinearMap (V i).toContinuousLinearMap (A i).1) = _ at ht
  rw [ht]
  exact (positive_norm_eq_trace (A i)).symm

theorem orthogonalSum_mono (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (A B : ∀ i, PositiveTraceClass (E i)) (h : ∀ i, (A i).1.1 ≤ (B i).1.1) :
    (orthogonalSum V A).1.1 ≤ (orthogonalSum V B).1.1 := by
  have he : (orthogonalSum V B).1 - (orthogonalSum V A).1 =
      ∑ i, (QuantumChannel.ofIsometry (V i)).toLinearMap ((B i).1-(A i).1) := by
    simp only [orthogonalSum_val, map_sub, Finset.sum_sub_distrib]
    rfl
  apply sub_nonneg.mp
  change 0 ≤ inclusionCLM ((orthogonalSum V B).1-(orthogonalSum V A).1)
  rw [he, map_sum]
  apply Finset.sum_nonneg
  intro i hi
  exact (QuantumChannel.ofIsometry (V i)).map_nonneg _ (sub_nonneg.mpr (h i))

variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- The actual orthogonal output fidelity is within η+2√δ of the classical
affinity times the common retained-sector fidelity. Components with zero
retained mass require no normalized-fidelity estimate. -/
theorem orthogonalSum_factorization_bound
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : OrthogonalFamily ℂ E V)
    (b : ∀ i, OrthonormalBasis (J i) ℂ (E i))
    (X C B : ∀ i, PositiveTraceClass (E i)) (p r : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i)
    (hps : ∑ i, p i = 1) (hXs : ∑ i, ‖(X i).1‖ ≤ 1)
    (hC : ∀ i, ‖(C i).1‖ = 1) (hB : ∀ i, ‖(B i).1‖ = 1)
    (hle : ∀ i, (PositiveTraceClass.scale ⟨r i, hr i⟩ (C i)).1.1 ≤ (X i).1.1)
    (c η : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ i, 0 < r i → |(C i).rootFidelity (B i)-c| ≤ η) :
    |(orthogonalSum V X).rootFidelity
        (orthogonalSum V (fun i ↦ PositiveTraceClass.scale ⟨p i,hp i⟩ (B i))) -
      c * Cloning.BlockFidelity.classicalAffinity (fun i ↦ ‖(X i).1‖) p| ≤
      η + 2 * Real.sqrt (∑ i, (‖(X i).1‖-r i)) := by
  let G i := PositiveTraceClass.scale ⟨r i,hr i⟩ (C i)
  let T i := PositiveTraceClass.scale ⟨p i,hp i⟩ (B i)
  have hG i : ‖(G i).1‖ = r i := by
    simp only [G, PositiveTraceClass.norm_scale, hC, mul_one]
    rfl
  have hT i : ‖(T i).1‖ = p i := by
    simp only [T, PositiveTraceClass.norm_scale, hB, mul_one]
    rfl
  have hmass : ‖(orthogonalSum V T).1‖ = 1 := by
    rw [norm_orthogonalSum]
    simpa only [hT] using hps
  have hri i : r i ≤ ‖(X i).1‖ := by
    have hn := norm_nonneg ((X i).1-(G i).1)
    rw [norm_positive_sub (X i) (G i) (hle i), hG] at hn
    linarith
  apply Cloning.BlockFidelity.lifted_factorization_bound p (fun i ↦ ‖(X i).1‖) r
    (fun i ↦ (C i).rootFidelity (B i)) _ c η hp hr hri hps hXs hc0 hc1 hη hsector
  have hf := PositiveTraceClass.rootFidelity_continuity
    (orthogonalSum V X) (orthogonalSum V T) (orthogonalSum V G) (orthogonalSum V T)
  rw [sub_self, norm_zero, Real.sqrt_zero, zero_mul, add_zero, hmass, Real.sqrt_one, mul_one,
    norm_positive_sub _ _ (orthogonalSum_mono V G X hle), norm_orthogonalSum,
    norm_orthogonalSum, ← Finset.sum_sub_distrib] at hf
  simp only [hG] at hf
  have he := rootFidelity_orthogonalSum V hV b G T
  simp only [G, T, PositiveTraceClass.rootFidelity_scale] at he
  rw [he] at hf
  exact hf

end Cloning.InfiniteFidelityHilbertSum
