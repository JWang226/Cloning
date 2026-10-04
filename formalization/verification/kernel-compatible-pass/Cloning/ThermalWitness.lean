import Cloning.BosonicNumberLaw
import Cloning.InfiniteDiagonalFidelity
import Cloning.InfiniteTraceClassPairing
import Cloning.InfiniteFidelityRegularized
import Mathlib.Analysis.Normed.Operator.Compact

/-! The thermal fidelity witness as a genuine positive compact operator. Its moments are
analytic trace pairings, evaluated by convergent number-basis series. -/

namespace Cloning.ThermalWitness

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter Cloning Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
open Cloning.InfiniteOccupationStates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma witness_summable {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    Summable (Thermal.witness q x) := by
  have hx0 : 0 < x := hq0.trans hqx
  have hr : ‖Real.sqrt (q / x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using (div_lt_one hx0).mpr hqx
  have hs := (summable_geometric_of_norm_lt_one hr).mul_left
    (Real.sqrt ((1 - q) / (1 - x)))
  exact hs.congr (fun n => (Thermal.witness_closed hq0.le (hqx.trans hx1) hx0.le hx1 n).symm)

def witnessTraceClass (b : HilbertBasis ℕ ℂ H) (q x : ℝ) : TraceClass H :=
  vectorMixture b (Thermal.witness q x)

def witnessOperator (b : HilbertBasis ℕ ℂ H) (q x : ℝ) : H →L[ℂ] H :=
  (witnessTraceClass b q x).1

lemma witnessOperator_apply_basis (b : HilbertBasis ℕ ℂ H) {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) (n : ℕ) :
    witnessOperator b q x (b n) = (Thermal.witness q x n : ℂ) • b n :=
  vectorMixture_apply_basis b _ (witness_summable hq0 hqx hx1) n

lemma witnessOperator_nonneg (b : HilbertBasis ℕ ℂ H) {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) : 0 ≤ witnessOperator b q x :=
  vectorMixture_nonneg b b.orthonormal.norm_eq_one _ (witness_summable hq0 hqx hx1)
    (fun n => (Thermal.witness_pos hq0 (hqx.trans hx1) (hq0.trans hqx) hx1 n).le)

omit [CompleteSpace H] in
lemma compact_rankOne (x y : H) : IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ x)).comp_clm (innerSL ℂ y)

lemma compact_vectorMixture {ι : Type*} (b : HilbertBasis ι ℂ H)
    (p : ι → ℝ) (hp : Summable p) : IsCompactOperator (vectorMixture b p).1 := by
  have hs := summable_weighted_projectors b b.orthonormal.norm_eq_one p hp
  have hlim := hs.hasSum.mapL inclusionCLM
  apply isCompactOperator_of_tendsto hlim
  apply Eventually.of_forall
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (isCompactOperator_zero (M₁ := H) (M₂ := H))
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi]
    apply IsCompactOperator.add _ hs
    simpa only [map_smul, inclusionCLM_apply, vectorProjector, TraceClass.ofOperator_coe] using
      (compact_rankOne (b i) (b i)).smul (p i : ℂ)

lemma witnessOperator_compact (b : HilbertBasis ℕ ℂ H) {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) : IsCompactOperator (witnessOperator b q x) :=
  compact_vectorMixture b _ (witness_summable hq0 hqx hx1)

/-- Trace evaluation for arbitrary index types, obtained by reindexing the basis by its range. -/
lemma trace_hasSum_basis {ι : Type*} (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (trace T hT) := by
  let e : ι ≃ Set.range b := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  have horth : Orthonormal ℂ (fun i : Set.range b => b (e.symm i)) :=
    b.orthonormal.comp e.symm e.symm.injective
  have hrange : Set.range (fun i : Set.range b => b (e.symm i)) = Set.range b := by
    exact e.symm.surjective.range_comp b
  let c : HilbertBasis (Set.range b) ℂ H := HilbertBasis.mk horth (by
    rw [hrange, b.dense_span])
  have hc : ∀ i, c i = b (e.symm i) := fun i => congrFun (HilbertBasis.coe_mk horth _) i
  have hs := (summable_trace_diagonal_of_isTraceClass hT c).hasSum
  rw [← trace_eq_of_hilbertBasis hT c] at hs
  have hs' := e.hasSum_iff.mpr hs
  exact hs'.congr (fun i => by simp only [Function.comp_apply, hc, e.symm_apply_apply])

/-- Every diagonal bounded observable tests only the actual number probabilities of an arbitrary
trace-class input; the input itself need not be diagonal. -/
lemma tracePairing_re_eq_number_moment {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A : TraceClass H) (W : H →L[ℂ] H) (w : ι → ℝ)
    (hW : ∀ i, W (b i) = (w i : ℂ) • b i) :
    (tracePairing A W).re = ∑' i, (⟪b i, A.1 (b i)⟫_ℂ).re * w i := by
  let hTC : IsTraceClass (A.1 * W) := isTraceClass_mul_mul (A := 1) (B := W) A.2
  change (trace (A.1 * W) hTC).re = _
  rw [← (trace_hasSum_basis b hTC).tsum_eq,
    Complex.re_tsum (trace_hasSum_basis b hTC).summable]
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.mul_apply, hW i, map_smul, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]

lemma diagonalMixture_tracePairing {ι : Type*} (b : HilbertBasis ι ℂ H)
    (p : ι → ℝ) (hp : Summable p) (W : H →L[ℂ] H) (w : ι → ℝ)
    (hW : ∀ i, W (b i) = (w i : ℂ) • b i) :
    (tracePairing (vectorMixture b p) W).re = ∑' i, p i * w i := by
  rw [tracePairing_re_eq_number_moment b _ W w hW]
  apply tsum_congr
  intro i
  rw [vectorMixture_apply_basis b p hp i, inner_smul_right,
    inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one i]
  simp

lemma amplified_thermal_witness_moment (b : HilbertBasis ℕ ℂ H) {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    (tracePairing (vectorMixture b (Thermal.geometric x)) (witnessOperator b q x)).re =
      Thermal.fidelity q x := by
  rw [diagonalMixture_tracePairing b _ (Thermal.geometric_hasSum (hq0.trans hqx).le hx1).summable
    _ _ (witnessOperator_apply_basis b hq0 hqx hx1)]
  exact (Thermal.witness_moment_hasSum hq0 (hqx.trans hx1) (hq0.trans hqx) hx1).tsum_eq

lemma inverse_apply_eigenvector {W : H →L[ℂ] H} (hW : IsStrictlyPositive W)
    {v : H} {a : ℝ} (ha : 0 < a) (hv : W v = (a : ℂ) • v) :
    CFC.rpow W (-1) v = (a⁻¹ : ℂ) • v := by
  have hprod : CFC.rpow W (-1) * W = 1 := by
    simpa only [CFC.rpow_one W hW.nonneg] using
      CFC.rpow_neg_mul_rpow (1 : ℝ) hW.isUnit hW.nonneg
  have hv' := congrArg (fun S : H →L[ℂ] H => S v) hprod
  simp only [ContinuousLinearMap.mul_apply, hv, map_smul, ContinuousLinearMap.one_apply] at hv'
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have h := congrArg (fun z : H => (a : ℂ)⁻¹ • z) hv'
  simpa only [smul_smul, inv_mul_cancel₀ haC, one_smul, Complex.ofReal_inv] using h

lemma regularized_witness_apply_basis (b : HilbertBasis ℕ ℂ H) {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) (ε : ℝ) (n : ℕ) :
    regularizedWeight (witnessOperator b q x) ε (b n) =
      ((Thermal.witness q x n + ε : ℝ) : ℂ) • b n := by
  simp only [regularizedWeight, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    witnessOperator_apply_basis b hq0 hqx hx1 n, Complex.ofReal_add, add_smul,
    Complex.coe_smul]

lemma regularized_inverse_witness_apply_basis (b : HilbertBasis ℕ ℂ H) {q x ε : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) (hε : 0 < ε) (n : ℕ) :
    CFC.rpow (regularizedWeight (witnessOperator b q x) ε) (-1) (b n) =
      (((Thermal.witness q x n + ε)⁻¹ : ℝ) : ℂ) • b n :=
  by
  simpa only [Complex.ofReal_inv] using inverse_apply_eigenvector
    (regularizedWeight_strictlyPositive (witnessOperator_nonneg b hq0 hqx hx1) hε)
    (add_pos (Thermal.witness_pos hq0 (hqx.trans hx1) (hq0.trans hqx) hx1 n) hε)
    (regularized_witness_apply_basis b hq0 hqx hx1 ε n)

/-- The inverse witness is handled through actual bounded inverses of positive
regularizations. Their moments are uniformly bounded by the exact thermal affinity. -/
lemma thermal_regularized_inverse_moment (b : HilbertBasis ℕ ℂ H) {q x ε : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) (hε : 0 < ε) :
    (tracePairing (vectorMixture b (Thermal.geometric q))
      (CFC.rpow (regularizedWeight (witnessOperator b q x) ε) (-1))).re ≤
        Thermal.fidelity q x := by
  rw [diagonalMixture_tracePairing b _ (Thermal.geometric_hasSum hq0.le (hqx.trans hx1)).summable
    _ _ (regularized_inverse_witness_apply_basis b hq0 hqx hx1 hε)]
  have hs := Thermal.witness_inverse_moment_hasSum hq0 (hqx.trans hx1) (hq0.trans hqx) hx1
  have hbound (n : ℕ) : Thermal.geometric q n * (Thermal.witness q x n + ε)⁻¹ ≤
      Thermal.geometric q n / Thermal.witness q x n := by
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (Thermal.geometric_nonneg hq0.le (hqx.trans hx1).le n)
      (Thermal.witness_pos hq0 (hqx.trans hx1) (hq0.trans hqx) hx1 n)
      (le_add_of_nonneg_right hε.le)
  have hn (n : ℕ) : 0 ≤ Thermal.geometric q n * (Thermal.witness q x n + ε)⁻¹ :=
    mul_nonneg (Thermal.geometric_nonneg hq0.le (hqx.trans hx1).le n)
      (inv_nonneg.mpr (add_nonneg
        (Thermal.witness_pos hq0 (hqx.trans hx1) (hq0.trans hqx) hx1 n).le hε.le))
  have hs' := hs.summable.of_nonneg_of_le hn hbound
  exact (hs'.tsum_le_tsum hbound hs.summable).trans_eq hs.tsum_eq

/-- Concrete thermal witness inequality for every actual positive trace-class input.
The regularized inverse moment is proved from its geometric series, not assumed. -/
lemma fidelity_sq_le_thermal_witness (b : HilbertBasis ℕ ℂ H) (A : TraceClass H)
    (hA : 0 ≤ A.1) {q x : ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    fidelity A.1 (vectorMixture b (Thermal.geometric q)).1 hA
      (vectorMixture_nonneg b b.orthonormal.norm_eq_one _
        (Thermal.geometric_hasSum hq0.le (hqx.trans hx1)).summable
        (Thermal.geometric_nonneg hq0.le (hqx.trans hx1).le))
      A.2 (vectorMixture b (Thermal.geometric q)).2 ^ 2 ≤
      (tracePairing A (witnessOperator b q x)).re * Thermal.fidelity q x := by
  apply fidelity_sq_le_of_regularized_inverse_moment hA _
    (witnessOperator_nonneg b hq0 hqx hx1) A.2 _
    (Thermal.fidelity_pos hq0.le (hqx.trans hx1) (hq0.trans hqx).le hx1).le
  intro ε hε
  exact thermal_regularized_inverse_moment b hq0 hqx hx1 hε

/-- Uniform inverse moment for any positive diagonal bounded witness, with its
possibly unbounded inverse represented only by a convergent scalar moment. -/
lemma diagonal_regularized_inverse_moment {ι : Type*} (b : HilbertBasis ι ℂ H)
    (p w : ι → ℝ) (hp : Summable p) (hp0 : ∀ i, 0 ≤ p i) (hw0 : ∀ i, 0 < w i)
    (W : H →L[ℂ] H) (hW0 : 0 ≤ W) (hW : ∀ i, W (b i) = (w i : ℂ) • b i)
    {M ε : ℝ} (hs : HasSum (fun i => p i / w i) M) (hε : 0 < ε) :
    (tracePairing (vectorMixture b p) (CFC.rpow (regularizedWeight W ε) (-1))).re ≤ M := by
  have hreg (i : ι) : regularizedWeight W ε (b i) = ((w i + ε : ℝ) : ℂ) • b i := by
    simp only [regularizedWeight, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, hW i, Complex.ofReal_add, add_smul, Complex.coe_smul]
  have hinv (i : ι) : CFC.rpow (regularizedWeight W ε) (-1) (b i) =
      (((w i + ε)⁻¹ : ℝ) : ℂ) • b i := by
    simpa only [Complex.ofReal_inv] using inverse_apply_eigenvector
      (regularizedWeight_strictlyPositive hW0 hε) (add_pos (hw0 i) hε) (hreg i)
  rw [diagonalMixture_tracePairing b p hp _ _ hinv]
  have hb (i : ι) : p i * (w i + ε)⁻¹ ≤ p i / w i := by
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (hp0 i) (hw0 i) (le_add_of_nonneg_right hε.le)
  have hn (i : ι) : 0 ≤ p i * (w i + ε)⁻¹ :=
    mul_nonneg (hp0 i) (inv_nonneg.mpr (add_pos (hw0 i) hε).le)
  exact ((hs.summable.of_nonneg_of_le hn hb).tsum_le_tsum hb hs.summable).trans_eq hs.tsum_eq

def productWitness {s : ℕ} (q x : Fin s → ℝ) (k : Fin s → ℕ) : ℝ :=
  ∏ i, Thermal.witness (q i) (x i) (k i)

def productGeometric {s : ℕ} (q : Fin s → ℝ) (k : Fin s → ℕ) : ℝ :=
  ∏ i, Thermal.geometric (q i) (k i)

lemma productWitness_pos {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (k : Fin s → ℕ) : 0 < productWitness q x k :=
  Finset.prod_pos (fun i _ => Thermal.witness_pos (hq0 i) ((hqx i).trans (hx1 i))
    ((hq0 i).trans (hqx i)) (hx1 i) (k i))

lemma productWitness_summable {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    Summable (productWitness q x) :=
  (Thermal.hasSum_fin_product s (fun i => Thermal.witness (q i) (x i))
    (fun i => ∑' n, Thermal.witness (q i) (x i) n)
    (fun i n => (Thermal.witness_pos (hq0 i) ((hqx i).trans (hx1 i))
      ((hq0 i).trans (hqx i)) (hx1 i) n).le)
    (fun i => (witness_summable (hq0 i) (hqx i) (hx1 i)).hasSum)).summable

def productWitnessOperator {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    (q x : Fin s → ℝ) : H →L[ℂ] H := (vectorMixture b (productWitness q x)).1

lemma productWitnessOperator_apply_basis {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) (k : Fin s → ℕ) :
    productWitnessOperator b q x (b k) = (productWitness q x k : ℂ) • b k :=
  vectorMixture_apply_basis b _ (productWitness_summable hq0 hqx hx1) k

lemma productWitnessOperator_nonneg {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) : 0 ≤ productWitnessOperator b q x :=
  vectorMixture_nonneg b b.orthonormal.norm_eq_one _ (productWitness_summable hq0 hqx hx1)
    (fun k => (productWitness_pos hq0 hqx hx1 k).le)

lemma productWitnessOperator_compact {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) : IsCompactOperator (productWitnessOperator b q x) :=
  compact_vectorMixture b _ (productWitness_summable hq0 hqx hx1)

lemma productGeometric_hasSum {s : ℕ} {q : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) : HasSum (productGeometric q) 1 :=
  Thermal.multimode_geometric_hasSum hq0 hq1

lemma productGeometric_nonneg {s : ℕ} {q : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (k : Fin s → ℕ) :
    0 ≤ productGeometric q k :=
  Finset.prod_nonneg (fun i _ => Thermal.geometric_nonneg (hq0 i) (hq1 i).le (k i))

lemma product_inverse_moment_hasSum {s : ℕ} {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1) :
    HasSum (fun k => productGeometric q k / productWitness q x k)
      (∏ i, Thermal.fidelity (q i) (x i)) := by
  simpa only [productGeometric, productWitness, ← Finset.prod_div_distrib] using
    Thermal.hasSum_fin_product s
      (fun i n => Thermal.geometric (q i) n / Thermal.witness (q i) (x i) n)
      (fun i => Thermal.fidelity (q i) (x i))
      (fun i n => div_nonneg (Thermal.geometric_nonneg (hq0 i).le ((hqx i).trans (hx1 i)).le n)
        (Thermal.witness_pos (hq0 i) ((hqx i).trans (hx1 i))
          ((hq0 i).trans (hqx i)) (hx1 i) n).le)
      (fun i => Thermal.witness_inverse_moment_hasSum (hq0 i) ((hqx i).trans (hx1 i))
        ((hq0 i).trans (hqx i)) (hx1 i))

lemma product_thermal_regularized_inverse_moment {s : ℕ}
    (b : HilbertBasis (Fin s → ℕ) ℂ H) {q x : Fin s → ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    {ε : ℝ} (hε : 0 < ε) :
    (tracePairing (vectorMixture b (productGeometric q))
      (CFC.rpow (regularizedWeight (productWitnessOperator b q x) ε) (-1))).re ≤
        ∏ i, Thermal.fidelity (q i) (x i) :=
  diagonal_regularized_inverse_moment b _ _
    (productGeometric_hasSum (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))).summable
    (productGeometric_nonneg (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i)))
    (productWitness_pos hq0 hqx hx1) _ (productWitnessOperator_nonneg b hq0 hqx hx1)
    (productWitnessOperator_apply_basis b hq0 hqx hx1)
    (product_inverse_moment_hasSum hq0 hqx hx1) hε

/-- Actual multimode compact-witness fidelity bound, including a correlated or
coherent arbitrary input operator. -/
lemma fidelity_sq_le_product_thermal_witness {s : ℕ}
    (b : HilbertBasis (Fin s → ℕ) ℂ H) (A : TraceClass H) (hA : 0 ≤ A.1)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) :
    fidelity A.1 (vectorMixture b (productGeometric q)).1 hA
      (vectorMixture_nonneg b b.orthonormal.norm_eq_one _
        (productGeometric_hasSum (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))).summable
        (productGeometric_nonneg (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))))
      A.2 (vectorMixture b (productGeometric q)).2 ^ 2 ≤
      (tracePairing A (productWitnessOperator b q x)).re * ∏ i, Thermal.fidelity (q i) (x i) := by
  apply fidelity_sq_le_of_regularized_inverse_moment hA _
    (productWitnessOperator_nonneg b hq0 hqx hx1) A.2 _
    (Finset.prod_nonneg (fun i _ =>
      (Thermal.fidelity_pos (hq0 i).le ((hqx i).trans (hx1 i))
        ((hq0 i).trans (hqx i)).le (hx1 i)).le))
  intro ε hε
  exact product_thermal_regularized_inverse_moment b hq0 hqx hx1 hε

lemma positive_diagonal_injective {ι : Type*} (b : HilbertBasis ι ℂ H)
    {W : H →L[ℂ] H} (hW : 0 ≤ W) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (heig : ∀ i, W (b i) = (w i : ℂ) • b i) : Function.Injective W := by
  have hstar : W.adjoint = W := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using (IsSelfAdjoint.of_nonneg hW).star_eq
  have hker (v : H) (hv : W v = 0) : v = 0 := by
    apply b.repr.injective
    ext i
    rw [map_zero]
    change b.repr v i = 0
    rw [b.repr_apply_apply]
    have h := ContinuousLinearMap.adjoint_inner_left W v (b i)
    rw [hstar, heig i, inner_smul_left, hv, inner_zero_right] at h
    simp only [Complex.conj_ofReal] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr (hw i).ne')
  intro u v huv
  apply sub_eq_zero.mp
  exact hker (u - v) (by rw [map_sub, huv, sub_self])

lemma witnessOperator_injective (b : HilbertBasis ℕ ℂ H) {q x : ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) :
    Function.Injective (witnessOperator b q x) :=
  positive_diagonal_injective b (witnessOperator_nonneg b hq0 hqx hx1) _
    (fun n => Thermal.witness_pos hq0 (hqx.trans hx1) (hq0.trans hqx) hx1 n)
    (witnessOperator_apply_basis b hq0 hqx hx1)

lemma productWitnessOperator_injective {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) : Function.Injective (productWitnessOperator b q x) :=
  positive_diagonal_injective b (productWitnessOperator_nonneg b hq0 hqx hx1) _
    (productWitness_pos hq0 hqx hx1) (productWitnessOperator_apply_basis b hq0 hqx hx1)

lemma product_thermal_witness_moment {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    {q x : Fin s → ℝ} (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i)
    (hx1 : ∀ i, x i < 1) :
    (tracePairing (vectorMixture b (productGeometric x)) (productWitnessOperator b q x)).re =
      ∏ i, Thermal.fidelity (q i) (x i) := by
  rw [diagonalMixture_tracePairing b _
    (productGeometric_hasSum (fun i => ((hq0 i).trans (hqx i)).le) hx1).summable
    _ _ (productWitnessOperator_apply_basis b hq0 hqx hx1)]
  simpa only [productGeometric, productWitness, ← Finset.prod_mul_distrib] using
    (Thermal.multimode_witness_moment_hasSum hq0 (fun i => (hqx i).trans (hx1 i))
      (fun i => (hq0 i).trans (hqx i)) hx1).tsum_eq

/-- The least-noise witness bound follows from the explicit seeded number law,
even when the actual output operator has nonzero off-diagonal entries. -/
lemma number_law_witness_moment_le {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    (A : TraceClass H) {q x : Fin s → ℝ} {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c)
    (hdiag : ∀ k, (⟪b k, A.1 (b k)⟫_ℂ).re = BosonicNumberLaw.mixtureLaw x a k) :
    (tracePairing A (productWitnessOperator b q x)).re ≤
      c * ∏ i, Thermal.fidelity (q i) (x i) := by
  rw [tracePairing_re_eq_number_moment b A _ _
    (productWitnessOperator_apply_basis b hq0 hqx hx1)]
  simp_rw [hdiag]
  exact BosonicNumberLaw.mixtureLaw_witness_moment_le hq0 hqx hx1 ha0 ha

/-- The actual fidelity bound for an arbitrary correlated seeded output law.
No abstract moment or fidelity inequality is part of the hypotheses. -/
lemma fidelity_sq_le_of_number_law {s : ℕ} (b : HilbertBasis (Fin s → ℕ) ℂ H)
    (A : TraceClass H) (hA : 0 ≤ A.1) {q x : Fin s → ℝ}
    {a : (Fin s → ℕ) → ℝ} {c : ℝ}
    (hq0 : ∀ i, 0 < q i) (hqx : ∀ i, q i < x i) (hx1 : ∀ i, x i < 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c)
    (hdiag : ∀ k, (⟪b k, A.1 (b k)⟫_ℂ).re = BosonicNumberLaw.mixtureLaw x a k) :
    fidelity A.1 (vectorMixture b (productGeometric q)).1 hA
      (vectorMixture_nonneg b b.orthonormal.norm_eq_one _
        (productGeometric_hasSum (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))).summable
        (productGeometric_nonneg (fun i => (hq0 i).le) (fun i => (hqx i).trans (hx1 i))))
      A.2 (vectorMixture b (productGeometric q)).2 ^ 2 ≤
      c * (∏ i, Thermal.fidelity (q i) (x i)) ^ 2 := by
  have hf0 : 0 ≤ ∏ i, Thermal.fidelity (q i) (x i) := Finset.prod_nonneg (fun i _ =>
    (Thermal.fidelity_pos (hq0 i).le ((hqx i).trans (hx1 i))
      ((hq0 i).trans (hqx i)).le (hx1 i)).le)
  calc
    _ ≤ _ := fidelity_sq_le_product_thermal_witness b A hA hq0 hqx hx1
    _ ≤ (c * ∏ i, Thermal.fidelity (q i) (x i)) * ∏ i, Thermal.fidelity (q i) (x i) :=
      mul_le_mul_of_nonneg_right (number_law_witness_moment_le b A hq0 hqx hx1 ha0 ha hdiag) hf0
    _ = _ := by ring

lemma trace_real_hasSum_basis {ι : Type*} (b : HilbertBasis ι ℂ H) (A : TraceClass H) :
    HasSum (fun i => (⟪b i, A.1 (b i)⟫_ℂ).re) (trace A.1 A.2).re :=
  (trace_hasSum_basis b A.2).map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous

lemma single_mixture_witness_moment_le {q x c : ℝ} {a : ℕ → ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c) :
    (∑' k, (∑' l, a l * BosonicNumberLaw.seededLaw x l k) * Thermal.witness q x k) ≤
      c * Thermal.fidelity q x := by
  let e : (Fin 1 → ℕ) ≃ ℕ := Equiv.funUnique (Fin 1) ℕ
  have he (l : Fin 1 → ℕ) : e l = l 0 := rfl
  have ha' : HasSum (fun l : Fin 1 → ℕ => a (l 0)) c := by
    simpa only [Function.comp_apply, he] using e.hasSum_iff.mpr ha
  have h := BosonicNumberLaw.mixtureLaw_witness_moment_le
    (q := fun _ : Fin 1 => q) (x := fun _ => x) (a := fun l => a (l 0))
    (fun _ => hq0) (fun _ => hqx) (fun _ => hx1) (fun l => ha0 (l 0)) ha'
  simp only [BosonicNumberLaw.mixtureLaw, BosonicNumberLaw.productLaw, Fin.prod_univ_one] at h
  have hinner (k : ℕ) : (∑' l : Fin 1 → ℕ, a (l 0) * BosonicNumberLaw.seededLaw x (l 0) k) =
      ∑' l, a l * BosonicNumberLaw.seededLaw x l k :=
    e.tsum_eq (fun l => a l * BosonicNumberLaw.seededLaw x l k)
  simp_rw [hinner] at h
  have houter := e.tsum_eq (fun k =>
    (∑' l, a l * BosonicNumberLaw.seededLaw x l k) * Thermal.witness q x k)
  rw [show (∑' k : Fin 1 → ℕ,
      (∑' l, a l * BosonicNumberLaw.seededLaw x l (k 0)) * Thermal.witness q x (k 0)) =
      (∑' k, (∑' l, a l * BosonicNumberLaw.seededLaw x l k) * Thermal.witness q x k)
    from houter] at h
  exact h

lemma single_number_law_witness_moment_le (b : HilbertBasis ℕ ℂ H) (A : TraceClass H)
    {q x c : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1)
    (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c)
    (hdiag : ∀ k, (⟪b k, A.1 (b k)⟫_ℂ).re =
      ∑' l, a l * BosonicNumberLaw.seededLaw x l k) :
    (tracePairing A (witnessOperator b q x)).re ≤ c * Thermal.fidelity q x := by
  rw [tracePairing_re_eq_number_moment b A _ _ (witnessOperator_apply_basis b hq0 hqx hx1)]
  simp_rw [hdiag]
  exact single_mixture_witness_moment_le hq0 hqx hx1 ha0 ha

lemma fidelity_sq_le_of_single_number_law (b : HilbertBasis ℕ ℂ H)
    (A : TraceClass H) (hA : 0 ≤ A.1) {q x c : ℝ} {a : ℕ → ℝ}
    (hq0 : 0 < q) (hqx : q < x) (hx1 : x < 1) (ha0 : ∀ l, 0 ≤ a l) (ha : HasSum a c)
    (hdiag : ∀ k, (⟪b k, A.1 (b k)⟫_ℂ).re =
      ∑' l, a l * BosonicNumberLaw.seededLaw x l k) :
    fidelity A.1 (vectorMixture b (Thermal.geometric q)).1 hA
      (vectorMixture_nonneg b b.orthonormal.norm_eq_one _
        (Thermal.geometric_hasSum hq0.le (hqx.trans hx1)).summable
        (Thermal.geometric_nonneg hq0.le (hqx.trans hx1).le))
      A.2 (vectorMixture b (Thermal.geometric q)).2 ^ 2 ≤
      c * Thermal.fidelity q x ^ 2 := by
  have hf0 := (Thermal.fidelity_pos hq0.le (hqx.trans hx1) (hq0.trans hqx).le hx1).le
  calc
    _ ≤ _ := fidelity_sq_le_thermal_witness b A hA hq0 hqx hx1
    _ ≤ (c * Thermal.fidelity q x) * Thermal.fidelity q x :=
      mul_le_mul_of_nonneg_right
        (single_number_law_witness_moment_le b A hq0 hqx hx1 ha0 ha hdiag) hf0
    _ = _ := by ring

end
end Cloning.ThermalWitness
