import Cloning.InfiniteChannelWeakLimit
import Cloning.InfiniteChannelTraceRepair
import Cloning.InfiniteChannelCovariance
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual Kraus channels from a strongly normalized family of bounded operators.
The infinite sum converges in the genuine trace norm. Complete positivity,
linearity, and trace preservation are consequences, not structure premises. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-- A single Kraus summand, bundled as a continuous trace-class map. -/
def krausTerm (K : H →L[ℂ] H) : TraceClass H →L[ℂ] TraceClass H :=
  sandwichCLM K (star K)

lemma krausTerm_nonneg (K : H →L[ℂ] H) (A : TraceClass H) (hA : 0 ≤ A.1) :
    0 ≤ (krausTerm K A).1 := star_right_conjugate_nonneg hA K

lemma krausTerm_vectorProjector (K : H →L[ℂ] H) (x : H) :
    krausTerm K (vectorProjector x) = vectorProjector (K x) := by
  apply Subtype.ext
  ext y
  change K (⟪x, (star K) y⟫_ℂ • x) = ⟪K x, y⟫_ℂ • K x
  rw [map_smul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

lemma krausTerm_completelyPositive (K : H →L[ℂ] H) :
    IsCompletelyPositive (krausTerm K).toLinearMap := by
  intro n A hA x
  convert hA (fun i => star K (x i)) using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact inner_sandwichCLM K (star K) (A i j) (x i) (x j)

/-- Strong normalization of the Kraus family, tested on actual Hilbert vectors. -/
def KrausComplete (K : ι → H →L[ℂ] H) : Prop :=
  ∀ x : H, HasSum (fun k => ‖K k x‖ ^ 2) (‖x‖ ^ 2)

/-- Positive inputs have an absolutely convergent Kraus series, with total
trace-norm mass exactly their input trace. The proof uses the actual rank-one
trace-norm decomposition and nonnegative Fubini. -/
theorem krausTerm_norm_hasSum_of_nonneg (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    HasSum (fun k => ‖krausTerm (K k) A‖) ‖A‖ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let v : w → H := fun i => CFC.sqrt A.1 (b i)
  have hmass : HasSum (fun i : w => ‖v i‖ ^ 2) ‖A‖ := by
    simpa only [norm_vectorProjector, TraceClass.norm_eq_trace_re_of_nonneg A hA]
      using positive_rankOne_mass hA A.2 b
  have hd : Summable (fun p : w × ι => ‖K p.2 (v p.1)‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg ‖K p.2 (v p.1)‖)).mpr
    refine ⟨fun i => (hK (v i)).summable, ?_⟩
    simpa only [(hK _).tsum_eq] using hmass.summable
  have hrow (k : ι) : HasSum (fun i : w => ‖K k (v i)‖ ^ 2)
      (traceCLM (krausTerm (K k) A)).re := by
    have h := ((positive_rankOne_series hA A.2 b).mapL (krausTerm (K k))).mapL traceCLM
    have hr := Complex.hasSum_re h
    simpa only [krausTerm_vectorProjector, traceCLM_vectorProjector, Complex.ofReal_re] using hr
  have heq (k : ι) : ‖krausTerm (K k) A‖ = ∑' i : w, ‖K k (v i)‖ ^ 2 := by
    rw [TraceClass.norm_eq_trace_re_of_nonneg _ (krausTerm_nonneg (K k) A hA)]
    exact (hrow k).tsum_eq.symm
  have hs : Summable (fun k => ‖krausTerm (K k) A‖) := by
    simpa only [heq] using hd.prod_symm.prod
  have ht : (∑' k, ‖krausTerm (K k) A‖) = ‖A‖ := by
    simp_rw [heq]
    rw [hd.tsum_comm]
    simpa only [(hK _).tsum_eq] using hmass.tsum_eq
  exact ht ▸ hs.hasSum

/-- Every trace-class input has a convergent Kraus series. Positivity is
removed by the actual Jordan and real/imaginary decompositions. -/
theorem krausTerm_summable (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) : Summable (fun k => krausTerm (K k) A) := by
  have hpos (B : TraceClass H) (hB : 0 ≤ B.1) :
      Summable (fun k => krausTerm (K k) B) :=
    (krausTerm_norm_hasSum_of_nonneg K hK B hB).summable.of_norm
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) :
      Summable (fun k => krausTerm (K k) B) := by
    have hp := hpos (TraceClass.positivePart B hB) (TraceClass.positivePart_nonneg B hB)
    have hn := hpos (TraceClass.negativePart B hB) (TraceClass.negativePart_nonneg B hB)
    convert hp.sub hn using 1
    ext k
    rw [← map_sub, TraceClass.positivePart_sub_negativePart]
  have hr := hself (TraceClass.realComponent A) (TraceClass.realComponent_isSelfAdjoint A)
  have hi := hself (TraceClass.imaginaryComponent A) (TraceClass.imaginaryComponent_isSelfAdjoint A)
  convert hr.add (hi.const_smul Complex.I) using 1
  ext k
  rw [← map_smul, ← map_add, TraceClass.realComponent_add_I_smul_imaginaryComponent]

/-- The Kraus series is complex linear on the whole trace-class space. -/
def krausLinearMap (K : ι → H →L[ℂ] H) (hK : KrausComplete K) :
    TraceClass H →ₗ[ℂ] TraceClass H where
  toFun A := ∑' k, krausTerm (K k) A
  map_add' A B := by
    simp only [map_add]
    exact (krausTerm_summable K hK A).tsum_add (krausTerm_summable K hK B)
  map_smul' c A := by
    simp only [map_smul]
    exact (krausTerm_summable K hK A).tsum_const_smul c

@[simp] lemma krausLinearMap_apply (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) : krausLinearMap K hK A = ∑' k, krausTerm (K k) A := rfl

lemma krausLinearMap_hasSum (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) : HasSum (fun k => krausTerm (K k) A) (krausLinearMap K hK A) :=
  (krausTerm_summable K hK A).hasSum

lemma krausLinearMap_nonneg (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) (hA : 0 ≤ A.1) : 0 ≤ (krausLinearMap K hK A).1 := by
  change 0 ≤ inclusionCLM (krausLinearMap K hK A)
  rw [krausLinearMap_apply, ContinuousLinearMap.map_tsum _ (krausTerm_summable K hK A)]
  exact tsum_nonneg (fun k => krausTerm_nonneg (K k) A hA)

private lemma traceCLM_eq_norm_of_nonneg (A : TraceClass H) (hA : 0 ≤ A.1) :
    traceCLM A = (‖A‖ : ℂ) := trace_eq_traceNorm_of_nonneg hA A.2

lemma krausLinearMap_trace_of_nonneg (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) (hA : 0 ≤ A.1) : traceCLM (krausLinearMap K hK A) = traceCLM A := by
  have hsource := (krausLinearMap_hasSum K hK A).mapL traceCLM
  have htarget : HasSum (fun k => traceCLM (krausTerm (K k) A)) (traceCLM A) := by
    simp only [traceCLM_eq_norm_of_nonneg A hA,
      traceCLM_eq_norm_of_nonneg _ (krausTerm_nonneg _ A hA)]
    exact Complex.hasSum_ofReal.mpr (krausTerm_norm_hasSum_of_nonneg K hK A hA)
  exact hsource.unique htarget

/-- Trace preservation holds for all trace-class operators, including
non-self-adjoint inputs. -/
lemma krausLinearMap_trace (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) : traceCLM (krausLinearMap K hK A) = traceCLM A := by
  let D : TraceClass H →ₗ[ℂ] ℂ :=
    traceCLM.toLinearMap.comp (krausLinearMap K hK) - traceCLM.toLinearMap
  have hpos (B : TraceClass H) (hB : 0 ≤ B.1) : D B = 0 :=
    sub_eq_zero.mpr (krausLinearMap_trace_of_nonneg K hK B hB)
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) : D B = 0 := by
    rw [← TraceClass.positivePart_sub_negativePart B hB, map_sub,
      hpos _ (TraceClass.positivePart_nonneg B hB),
      hpos _ (TraceClass.negativePart_nonneg B hB), sub_self]
  have hzero : D A = 0 := by
    rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent A, map_add, map_smul,
      hself _ (TraceClass.realComponent_isSelfAdjoint A),
      hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)]
    simp
  exact sub_eq_zero.mp hzero

/-- Complete positivity follows from finite Kraus sums and their actual
trace-norm (hence weak-operator) convergence, at every finite ancilla size. -/
lemma krausLinearMap_completelyPositive (K : ι → H →L[ℂ] H) (hK : KrausComplete K) :
    IsCompletelyPositive (krausLinearMap K hK) := by
  classical
  let F : Finset ι → TraceClass H →ₗ[ℂ] TraceClass H := fun s =>
    ∑ k ∈ s, (krausTerm (K k)).toLinearMap
  have hF (s : Finset ι) : IsCompletelyPositive (F s) := by
    induction s using Finset.induction_on with
    | empty =>
      intro n A hA x
      simp [F]
    | @insert k s hk ih =>
      simpa only [F, Finset.sum_insert hk] using (krausTerm_completelyPositive (K k)).add ih
  intro n A hA
  apply BlockPositive.of_weakOperator_tendsto (l := (atTop : Filter (Finset ι)))
    (fun s i j => F s (A i j)) (fun i j => krausLinearMap K hK (A i j))
    (fun s => hF s n A hA)
  intro i j x y
  have h := (traceClassMatrixCoefficient x y).continuous.tendsto
    (krausLinearMap K hK (A i j)) |>.comp (krausLinearMap_hasSum K hK (A i j))
  simpa only [F, LinearMap.sum_apply, traceClassMatrixCoefficient_apply] using h

/-- A genuine infinite-dimensional quantum channel produced from Kraus
normalization alone. -/
def QuantumChannel.ofKraus (K : ι → H →L[ℂ] H) (hK : KrausComplete K) :
    QuantumChannel H H where
  toLinearMap := krausLinearMap K hK
  map_nonneg := krausLinearMap_nonneg K hK
  trace_preserving := krausLinearMap_trace K hK
  completelyPositive := krausLinearMap_completelyPositive K hK

/-- The defining series converges in the trace-class Banach norm. -/
lemma QuantumChannel.ofKraus_hasSum (K : ι → H →L[ℂ] H) (hK : KrausComplete K)
    (A : TraceClass H) : HasSum (fun k => krausTerm (K k) A)
      ((QuantumChannel.ofKraus K hK).toLinearMap A) :=
  krausLinearMap_hasSum K hK A

end
end Cloning.InfiniteTraceClass
