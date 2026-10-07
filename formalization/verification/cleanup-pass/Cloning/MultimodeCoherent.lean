import Cloning.CoherentContinuity
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Actual multimode complex coherent vectors

Finite products of one-mode coefficient vectors define actual vectors in the
multimode occupation Hilbert space. Norms and inner products are proved by
absolutely convergent finite product sums. This includes zero modes, where the
occupation index type is a singleton and the coherent vector has coefficient one.
-/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology ENNReal
open Filter MeasureTheory

namespace Cloning.MultimodeCoherent

open Cloning Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev Fock (s : ℕ) := lp (fun _ : Fin s → ℕ ↦ ℂ) 2

/-- Finite tensor products of convergent complex series, with absolute
summability supplied by finite-dimensionality of the scalar field. -/
theorem hasSum_fin_product_complex (s : ℕ) (f : Fin s → ℕ → ℂ) (a : Fin s → ℂ)
    (hs : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun k : Fin s → ℕ ↦ ∏ i, f i (k i)) (∏ i, a i) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ht : HasSum (fun k : Fin s → ℕ ↦ ∏ i : Fin s, f i.succ (k i))
        (∏ i : Fin s, a i.succ) := ih (fun i ↦ f i.succ) (fun i ↦ a i.succ)
          (fun i ↦ hs i.succ)
    have hsum : Summable (fun k : ℕ × (Fin s → ℕ) ↦
        f 0 k.1 * ∏ i : Fin s, f i.succ (k.2 i)) :=
      summable_mul_of_summable_norm (f := f 0)
        (g := fun k : Fin s → ℕ ↦ ∏ i : Fin s, f i.succ (k i))
        (hs 0).summable.norm ht.summable.norm
    have hm : HasSum (fun k : ℕ × (Fin s → ℕ) ↦
        f 0 k.1 * ∏ i : Fin s, f i.succ (k.2 i)) (a 0 * ∏ i : Fin s, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun k : Fin s → ℕ ↦ ∏ i : Fin s, f i.succ (k i))
        (s := a 0) (t := ∏ i : Fin s, a i.succ) (hs 0) ht hsum
    rw [← (Fin.consEquiv (fun _ : Fin (s + 1) ↦ ℕ)).hasSum_iff]
    simpa [Fin.prod_univ_succ, Fin.consEquiv, Function.comp_def] using hm

theorem product_norm_sq_hasSum {s : ℕ} (x : Fin s → ComplexCoherent.Fock) :
    HasSum (fun k : Fin s → ℕ ↦ ‖∏ i, x i (k i)‖ ^ (2 : ℕ))
      (∏ i, ‖x i‖ ^ (2 : ℕ)) := by
  have hs (i : Fin s) : HasSum (fun n ↦ ‖x i n‖ ^ (2 : ℕ)) (‖x i‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (x i)
  simpa only [norm_prod, Finset.prod_pow] using
    Thermal.hasSum_fin_product s (fun i n ↦ ‖x i n‖ ^ (2 : ℕ))
      (fun i ↦ ‖x i‖ ^ (2 : ℕ)) (fun i n ↦ sq_nonneg _) hs

/-- The literal finite tensor product of arbitrary one-mode occupation vectors. -/
def tensorVector {s : ℕ} (x : Fin s → ComplexCoherent.Fock) : Fock s := by
  refine ⟨fun k ↦ ∏ i, x i (k i), memℓp_gen ?_⟩
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (product_norm_sq_hasSum x).summable

@[simp] theorem tensorVector_apply {s : ℕ} (x : Fin s → ComplexCoherent.Fock)
    (k : Fin s → ℕ) : tensorVector x k = ∏ i, x i (k i) := rfl

theorem tensorVector_norm {s : ℕ} (x : Fin s → ComplexCoherent.Fock) :
    ‖tensorVector x‖ = ∏ i, ‖x i‖ := by
  have hsq : ‖tensorVector x‖ ^ (2 : ℕ) = (∏ i, ‖x i‖) ^ (2 : ℕ) := by
    calc
      _ = ∑' k : Fin s → ℕ, ‖∏ i, x i (k i)‖ ^ (2 : ℕ) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tensorVector_apply] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (tensorVector x)
      _ = ∏ i, ‖x i‖ ^ (2 : ℕ) := (product_norm_sq_hasSum x).tsum_eq
      _ = _ := Finset.prod_pow _ _ _
  have hprod : 0 ≤ ∏ i, ‖x i‖ := Finset.prod_nonneg (fun i _ ↦ norm_nonneg _)
  nlinarith [norm_nonneg (tensorVector x)]

/-- Exact inner-product factorization, derived from actual ℓ² coefficients. -/
theorem inner_tensorVector {s : ℕ} (x y : Fin s → ComplexCoherent.Fock) :
    ⟪tensorVector x, tensorVector y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  have he (k : Fin s → ℕ) :
      ⟪tensorVector x k, tensorVector y k⟫_ℂ = ∏ i, ⟪x i (k i), y i (k i)⟫_ℂ := by
    simp only [tensorVector_apply, RCLike.inner_apply, map_prod, Finset.prod_mul_distrib]
  simp_rw [he]
  exact (hasSum_fin_product_complex s (fun i n ↦ ⟪x i n, y i n⟫_ℂ)
    (fun i ↦ ⟪x i, y i⟫_ℂ) (fun i ↦ lp.hasSum_inner (x i) (y i))).tsum_eq

/-- The genuine multimode coherent vector, with arbitrary complex amplitudes. -/
def coherentVector {s : ℕ} (z : Fin s → ℂ) : Fock s :=
  tensorVector (fun i ↦ ComplexCoherent.coherentVector (z i))

@[simp] theorem coherentVector_apply {s : ℕ} (z : Fin s → ℂ) (k : Fin s → ℕ) :
    coherentVector z k = ∏ i, ComplexCoherent.coherentVector (z i) (k i) := rfl

theorem coherentVector_coefficients {s : ℕ} (z : Fin s → ℂ) (k : Fin s → ℕ) :
    coherentVector z k = ∏ i, (Real.exp (-‖z i‖ ^ 2 / 2) : ℂ) * z i ^ k i /
      (Real.sqrt ((k i).factorial : ℝ) : ℂ) := by
  simp only [coherentVector_apply, ComplexCoherent.coherentVector_apply]

theorem coherentVector_norm {s : ℕ} (z : Fin s → ℂ) : ‖coherentVector z‖ = 1 := by
  simp only [coherentVector, tensorVector_norm, ComplexCoherent.coherentVector_norm,
    Finset.prod_const_one]

/-- The multimode coherent kernel is the product of the one-mode kernels. -/
theorem inner_coherentVector {s : ℕ} (z w : Fin s → ℂ) :
    ⟪coherentVector z, coherentVector w⟫_ℂ = ∏ i,
      Complex.exp (((-(‖z i‖ ^ 2 + ‖w i‖ ^ 2) / 2 : ℝ) : ℂ) +
        starRingEnd ℂ (z i) * w i) := by
  simp only [coherentVector, inner_tensorVector, ComplexCoherent.inner_coherentVector]

/-- Norm continuity holds jointly in all amplitudes, including zero amplitudes
and the empty tuple of modes. -/
theorem continuous_coherentVector (s : ℕ) : Continuous (@coherentVector s) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hn (w : Fin s → ℂ) : ‖coherentVector w - coherentVector z‖ ^ 2 =
      2 - 2 * (⟪coherentVector w, coherentVector z⟫_ℂ).re := by
    have h := norm_sub_sq (𝕜 := ℂ) (coherentVector w) (coherentVector z)
    simp only [coherentVector_norm, one_pow] at h
    change ‖coherentVector w - coherentVector z‖ ^ 2 =
      1 - 2 * (⟪coherentVector w, coherentVector z⟫_ℂ).re + 1 at h
    linarith
  have hs : Continuous (fun w : Fin s → ℂ ↦ ‖coherentVector w - coherentVector z‖ ^ 2) := by
    simp_rw [hn, inner_coherentVector]
    fun_prop
  have ht : Tendsto (fun w : Fin s → ℂ ↦ ‖coherentVector w - coherentVector z‖ ^ 2)
      (𝓝 z) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hs.tendsto z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

/-- The rank-one coherent operator as an element of the trace-class Banach space. -/
def coherentProjector {s : ℕ} (z : Fin s → ℂ) : TraceClass (Fock s) :=
  vectorProjector (coherentVector z)

theorem continuous_coherentProjector (s : ℕ) : Continuous (@coherentProjector s) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact vectorProjector_tendsto ((continuous_coherentVector s).tendsto z)

theorem coherentProjector_norm {s : ℕ} (z : Fin s → ℂ) : ‖coherentProjector z‖ = 1 := by
  rw [coherentProjector, norm_vectorProjector, coherentVector_norm, one_pow]

theorem coherentProjector_trace {s : ℕ} (z : Fin s → ℂ) : traceCLM (coherentProjector z) = 1 := by
  rw [coherentProjector, traceCLM_vectorProjector, coherentVector_norm, one_pow]
  rfl

theorem coherentProjector_nonneg {s : ℕ} (z : Fin s → ℂ) : 0 ≤ (coherentProjector z).1 := by
  change 0 ≤ InnerProductSpace.rankOne ℂ (coherentVector z) (coherentVector z)
  exact (InnerProductSpace.rankOne ℂ _ _).nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self _)

def coherentState {s : ℕ} (z : Fin s → ℂ) : DensityState (Fock s) :=
  DensityState.pure (coherentVector z) (coherentVector_norm z)

/-- Bochner integrability in the genuine Hilbert norm under any finite measure. -/
theorem integrable_coherentVector {s : ℕ} (μ : Measure (Fin s → ℂ)) [IsFiniteMeasure μ] :
    Integrable coherentVector μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_coherentVector s).aestronglyMeasurable
  exact Eventually.of_forall (fun z ↦ le_of_eq (coherentVector_norm z))

/-- The actual coherent density operators are Bochner integrable in trace norm. -/
theorem integrable_coherentProjector {s : ℕ} (μ : Measure (Fin s → ℂ)) [IsFiniteMeasure μ] :
    Integrable coherentProjector μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_coherentProjector s).aestronglyMeasurable
  exact Eventually.of_forall (fun z ↦ le_of_eq (coherentProjector_norm z))

end Cloning.MultimodeCoherent
