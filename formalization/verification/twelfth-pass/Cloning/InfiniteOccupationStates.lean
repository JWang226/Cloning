import Cloning.WernerAsymptotics
import Cloning.InfiniteTraceClassSeries

/-!
# Trace-norm Werner occupation limit

The actual binomial Werner occupation law defines a convergent series of
rank-one operators in the trace-class Banach space. Its thermal limit follows
from the proved binomial asymptotics and normalization, with no assumed
operator convergence. On an occupation Hilbert basis these are diagonal
occupation states. Identifying the physical Werner channel output with this
operator is a separate representation-theoretic obligation.
-/

noncomputable section
open scoped BigOperators Topology ComplexOrder
open Filter

namespace Cloning.InfiniteOccupationStates

set_option backward.isDefEq.respectTransparency false

open InfiniteTraceClass WernerNormalization WernerAsymptotics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isTraceClass_sub {A B : H →L[ℂ] H} (hA : IsTraceClass A) (hB : IsTraceClass B) :
    IsTraceClass (A - B) := by
  simpa only [sub_eq_add_neg] using isTraceClass_add hA (isTraceClass_neg hB)

/-- Finite support gives summability even in a finite initial segment where
the cloning inequality fails. -/
theorem occupationLaw_summable (n m s : ℕ) : Summable (occupationLaw n m s) := by
  have hs : HasSum (occupationLaw n m s)
      (∑ k ∈ occupationSupport s (m - n), occupationLaw n m s k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    unfold occupationLaw
    rw [if_neg]
    exact fun h => hk (mem_occupationSupport.mpr h)
  exact hs.summable

/-- A summable mixture of Hilbert-basis projectors is actually diagonal,
with the given coefficients as its eigenvalues. -/
theorem vectorMixture_apply_basis {ι : Type*} (b : HilbertBasis ι ℂ H)
    (p : ι → ℝ) (hp : Summable p) (i : ι) :
    (vectorMixture b p).1 (b i) = (p i : ℂ) • b i := by
  classical
  let L : TraceClass H →L[ℂ] H :=
    (ContinuousLinearMap.apply ℂ H (b i)).comp inclusionCLM
  change L (vectorMixture b p) = _
  rw [vectorMixture, L.map_tsum (summable_weighted_projectors b b.orthonormal.norm_eq_one p hp)]
  simp only [map_smul]
  have heval (j : ι) : L (vectorProjector (b j)) = if j = i then b i else 0 := by
    change InnerProductSpace.rankOne ℂ (b j) (b j) (b i) = _
    rw [InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal j i]
    split_ifs with hji
    · simp [hji]
    · simp
  simp_rw [heval]
  simp

/-- The finite Werner occupation series as an actual trace-class operator. -/
def occupationOperator {s : ℕ} (x : (Fin s → ℕ) → H) (n m : ℕ) : TraceClass H :=
  vectorMixture x (occupationLaw n m s)

/-- The infinite product-geometric mixture in the trace-class Banach space. -/
def thermalOperator {s : ℕ} (x : (Fin s → ℕ) → H) (γ : ℝ) : TraceClass H :=
  vectorMixture x (thermalLaw γ s)

theorem occupationOperator_apply_basis {s : ℕ}
    (b : HilbertBasis (Fin s → ℕ) ℂ H) (n m : ℕ) (k : Fin s → ℕ) :
    (occupationOperator b n m).1 (b k) = (occupationLaw n m s k : ℂ) • b k :=
  vectorMixture_apply_basis b _ (occupationLaw_summable n m s) k

theorem thermalOperator_apply_basis {s : ℕ}
    (b : HilbertBasis (Fin s → ℕ) ℂ H) {γ : ℝ} (hγ : 1 < γ) (k : Fin s → ℕ) :
    (thermalOperator b γ).1 (b k) = (thermalLaw γ s k : ℂ) • b k :=
  vectorMixture_apply_basis b _ (thermalLaw_hasSum hγ s).summable k

theorem occupationOperator_nonneg {s : ℕ} (x : (Fin s → ℕ) → H)
    (hx : ∀ k, ‖x k‖ = 1) (n m : ℕ) : 0 ≤ (occupationOperator x n m).1 :=
  vectorMixture_nonneg x hx _ (occupationLaw_summable n m s)
    (occupationLaw_nonneg n m s)

theorem thermalOperator_nonneg {s : ℕ} (x : (Fin s → ℕ) → H)
    (hx : ∀ k, ‖x k‖ = 1) {γ : ℝ} (hγ : 1 < γ) :
    0 ≤ (thermalOperator x γ).1 :=
  vectorMixture_nonneg x hx _ (thermalLaw_hasSum hγ s).summable
    (thermalLaw_nonneg hγ s)

/-- A normalized Werner occupation density operator, with proved positive
trace-class membership and unit trace. -/
def occupationState {s : ℕ} (hs : 1 ≤ s) (x : (Fin s → ℕ) → H)
    (hx : ∀ k, ‖x k‖ = 1) (n m : ℕ) (hnm : n ≤ m) : DensityState H :=
  DensityState.vectorMixture x hx (occupationLaw n m s)
    (occupationLaw_nonneg n m s) (occupationLaw_hasSum n m s hnm hs)

/-- The normalized infinite thermal occupation density operator. -/
def thermalState {s : ℕ} (x : (Fin s → ℕ) → H) (hx : ∀ k, ‖x k‖ = 1)
    (γ : ℝ) (hγ : 1 < γ) : DensityState H :=
  DensityState.vectorMixture x hx (thermalLaw γ s)
    (thermalLaw_nonneg hγ s) (thermalLaw_hasSum hγ s)

theorem occupationState_op {s : ℕ} (hs : 1 ≤ s) (x : (Fin s → ℕ) → H)
    (hx : ∀ k, ‖x k‖ = 1) (n m : ℕ) (hnm : n ≤ m) :
    (occupationState hs x hx n m hnm).op = (occupationOperator x n m).1 := rfl

theorem thermalState_op {s : ℕ} (x : (Fin s → ℕ) → H)
    (hx : ∀ k, ‖x k‖ = 1) (γ : ℝ) (hγ : 1 < γ) :
    (thermalState x hx γ hγ).op = (thermalOperator x γ).1 := rfl

/-- The quantitative classical-to-quantum bound for the actual occupation
operators. Orthogonality is not needed for this upper bound. -/
theorem occupation_norm_sub_le_l1 {s : ℕ} (x : (Fin s → ℕ) → H)
    (hx : ∀ k, ‖x k‖ = 1) (n m : ℕ) {γ : ℝ} (hγ : 1 < γ) :
    ‖occupationOperator x n m - thermalOperator x γ‖ ≤
      CountableScheffe.l1Distance (occupationLaw n m s) (thermalLaw γ s) :=
  norm_vectorMixture_sub_le_l1 x hx _ _ (occupationLaw_summable n m s)
    (thermalLaw_hasSum hγ s).summable

/-- The actual Werner occupation operators converge in the trace norm.
Only the cloning-ratio limit is assumed. -/
theorem occupation_norm_sub_tendsto {s : ℕ} (hs : 1 ≤ s)
    (x : (Fin s → ℕ) → H) (hx : ∀ k, ‖x k‖ = 1)
    (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ ‖occupationOperator x n (m n) - thermalOperator x γ‖)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ occupation_norm_sub_le_l1 x hx n (m n) hγ)
    (occupationLaw_l1_tendsto m hγ h s hs)

/-- Convergence in the genuine trace-class Banach space, rather than only
pointwise convergence of matrix elements or convergence of scalar weights. -/
theorem occupationOperator_tendsto {s : ℕ} (hs : 1 ≤ s)
    (x : (Fin s → ℕ) → H) (hx : ∀ k, ‖x k‖ = 1)
    (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ occupationOperator x n (m n)) atTop (𝓝 (thermalOperator x γ)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (occupation_norm_sub_tendsto hs x hx m hγ h)

/-- The same limit written explicitly with the analytic trace norm of the
underlying bounded operators. -/
theorem occupation_traceNorm_tendsto {s : ℕ} (hs : 1 ≤ s)
    (x : (Fin s → ℕ) → H) (hx : ∀ k, ‖x k‖ = 1)
    (m : ℕ → ℕ) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ traceNorm
      ((occupationOperator x n (m n)).1 - (thermalOperator x γ).1)
      (isTraceClass_sub (occupationOperator x n (m n)).2 (thermalOperator x γ).2))
      atTop (𝓝 0) :=
  occupation_norm_sub_tendsto hs x hx m hγ h

/-- When every output size is admissible, the convergence is between the
constructed unit-trace density operators at every index. -/
theorem occupationState_traceNorm_tendsto {s : ℕ} (hs : 1 ≤ s)
    (x : (Fin s → ℕ) → H) (hx : ∀ k, ‖x k‖ = 1)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ traceNorm
      ((occupationState hs x hx n (m n) (hm n)).op - (thermalState x hx γ hγ).op)
      (isTraceClass_sub (occupationState hs x hx n (m n) (hm n)).traceClass
        (thermalState x hx γ hγ).traceClass)) atTop (𝓝 0) :=
  occupation_traceNorm_tendsto hs x hx m hγ h

/-- Occupation Hilbert bases satisfy the unit-vector assumptions automatically. -/
theorem hilbertBasis_occupation_tendsto (D : ℕ) (hD : 2 ≤ D)
    (b : HilbertBasis (Fin (D - 1) → ℕ) ℂ H) (m : ℕ → ℕ)
    {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ occupationOperator b n (m n)) atTop (𝓝 (thermalOperator b γ)) :=
  occupationOperator_tendsto (by omega) b b.orthonormal.norm_eq_one m hγ h

end Cloning.InfiniteOccupationStates
