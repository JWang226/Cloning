import Cloning.InfiniteIsometricChannel
import Cloning.InfiniteChannelWeakLimit
import Cloning.InfiniteChannelCovariance
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Kraus channels between different Hilbert spaces, from actual vector
normalization. Rectangular conjugation and trace-norm convergence are derived. -/

namespace Cloning.InfiniteTraceClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

variable {H J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
variable {ι : Type*}

/-- Strong normalization of the Kraus family, tested on actual Hilbert vectors. -/
def RectangularKrausComplete (K : ι → H →L[ℂ] J) : Prop :=
  ∀ x : H, HasSum (fun k => ‖K k x‖ ^ 2) (‖x‖ ^ 2)

/-- Positive inputs have an absolutely convergent Kraus series, with total
trace-norm mass exactly their input trace. The proof uses the actual rank-one
trace-norm decomposition and nonnegative Fubini. -/
theorem rectangularKraus_norm_hasSum_of_nonneg (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) (hA : 0 ≤ A.1) :
    HasSum (fun k => ‖conjugationLinearMap (K k) A‖) ‖A‖ := by
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
      (traceCLM (conjugationLinearMap (K k) A)).re := by
    have h := (conjugationLinearMap_positive_hasSum (K k) A hA b).mapL traceCLM
    have hr := Complex.hasSum_re h
    simpa only [conjugationLinearMap_vectorProjector, traceCLM_vectorProjector, Complex.ofReal_re] using hr
  have heq (k : ι) : ‖conjugationLinearMap (K k) A‖ = ∑' i : w, ‖K k (v i)‖ ^ 2 := by
    rw [TraceClass.norm_eq_trace_re_of_nonneg _ (conjugationLinearMap_nonneg (K k) A hA)]
    exact (hrow k).tsum_eq.symm
  have hs : Summable (fun k => ‖conjugationLinearMap (K k) A‖) := by
    simpa only [heq] using hd.prod_symm.prod
  have ht : (∑' k, ‖conjugationLinearMap (K k) A‖) = ‖A‖ := by
    simp_rw [heq]
    rw [hd.tsum_comm]
    simpa only [(hK _).tsum_eq] using hmass.tsum_eq
  exact ht ▸ hs.hasSum

/-- Every trace-class input has a convergent Kraus series. Positivity is
removed by the actual Jordan and real/imaginary decompositions. -/
theorem rectangularKraus_summable (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) : Summable (fun k => conjugationLinearMap (K k) A) := by
  have hpos (B : TraceClass H) (hB : 0 ≤ B.1) :
      Summable (fun k => conjugationLinearMap (K k) B) :=
    (rectangularKraus_norm_hasSum_of_nonneg K hK B hB).summable.of_norm
  have hself (B : TraceClass H) (hB : IsSelfAdjoint B.1) :
      Summable (fun k => conjugationLinearMap (K k) B) := by
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
def rectangularKrausLinearMap (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K) :
    TraceClass H →ₗ[ℂ] TraceClass J where
  toFun A := ∑' k, conjugationLinearMap (K k) A
  map_add' A B := by
    simp only [map_add]
    exact (rectangularKraus_summable K hK A).tsum_add (rectangularKraus_summable K hK B)
  map_smul' c A := by
    simp only [map_smul]
    exact (rectangularKraus_summable K hK A).tsum_const_smul c

@[simp] lemma rectangularKrausLinearMap_apply (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) : rectangularKrausLinearMap K hK A = ∑' k, conjugationLinearMap (K k) A := rfl

lemma rectangularKrausLinearMap_hasSum (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) : HasSum (fun k => conjugationLinearMap (K k) A) (rectangularKrausLinearMap K hK A) :=
  (rectangularKraus_summable K hK A).hasSum

lemma rectangularKrausLinearMap_nonneg (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) (hA : 0 ≤ A.1) : 0 ≤ (rectangularKrausLinearMap K hK A).1 := by
  change 0 ≤ inclusionCLM (rectangularKrausLinearMap K hK A)
  rw [rectangularKrausLinearMap_apply, ContinuousLinearMap.map_tsum _ (rectangularKraus_summable K hK A)]
  exact tsum_nonneg (fun k => conjugationLinearMap_nonneg (K k) A hA)

private lemma traceCLM_eq_norm_of_nonneg (A : TraceClass H) (hA : 0 ≤ A.1) :
    traceCLM A = (‖A‖ : ℂ) := trace_eq_traceNorm_of_nonneg hA A.2

lemma rectangularKrausLinearMap_trace_of_nonneg (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) (hA : 0 ≤ A.1) : traceCLM (rectangularKrausLinearMap K hK A) = traceCLM A := by
  have hsource := (rectangularKrausLinearMap_hasSum K hK A).mapL traceCLM
  have htarget : HasSum (fun k => traceCLM (conjugationLinearMap (K k) A)) (traceCLM A) := by
    simp only [traceCLM_eq_norm_of_nonneg A hA,
      traceCLM_eq_norm_of_nonneg _ (conjugationLinearMap_nonneg _ A hA)]
    exact Complex.hasSum_ofReal.mpr (rectangularKraus_norm_hasSum_of_nonneg K hK A hA)
  exact hsource.unique htarget

/-- Trace preservation holds for all trace-class operators, including
non-self-adjoint inputs. -/
lemma rectangularKrausLinearMap_trace (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) : traceCLM (rectangularKrausLinearMap K hK A) = traceCLM A := by
  let D : TraceClass H →ₗ[ℂ] ℂ :=
    traceCLM.toLinearMap.comp (rectangularKrausLinearMap K hK) - traceCLM.toLinearMap
  have hpos (B : TraceClass H) (hB : 0 ≤ B.1) : D B = 0 :=
    sub_eq_zero.mpr (rectangularKrausLinearMap_trace_of_nonneg K hK B hB)
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
lemma rectangularKrausLinearMap_completelyPositive (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K) :
    IsCompletelyPositive (rectangularKrausLinearMap K hK) := by
  classical
  let F : Finset ι → TraceClass H →ₗ[ℂ] TraceClass J := fun s =>
    ∑ k ∈ s, conjugationLinearMap (K k)
  have hF (s : Finset ι) : IsCompletelyPositive (F s) := by
    induction s using Finset.induction_on with
    | empty =>
      intro n A hA x
      simp [F]
    | @insert k s hk ih =>
      simpa only [F, Finset.sum_insert hk] using (conjugationLinearMap_completelyPositive (K k)).add ih
  intro n A hA
  apply BlockPositive.of_weakOperator_tendsto (l := (atTop : Filter (Finset ι)))
    (fun s i j => F s (A i j)) (fun i j => rectangularKrausLinearMap K hK (A i j))
    (fun s => hF s n A hA)
  intro i j x y
  have h := (traceClassMatrixCoefficient x y).continuous.tendsto
    (rectangularKrausLinearMap K hK (A i j)) |>.comp (rectangularKrausLinearMap_hasSum K hK (A i j))
  simpa only [F, LinearMap.sum_apply, traceClassMatrixCoefficient_apply] using h

/-- A genuine infinite-dimensional quantum channel produced from Kraus
normalization alone. -/
def QuantumChannel.ofRectangularKraus (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K) :
    QuantumChannel H J where
  toLinearMap := rectangularKrausLinearMap K hK
  map_nonneg := rectangularKrausLinearMap_nonneg K hK
  trace_preserving := rectangularKrausLinearMap_trace K hK
  completelyPositive := rectangularKrausLinearMap_completelyPositive K hK

/-- The defining series converges in the trace-class Banach norm. -/
lemma QuantumChannel.ofRectangularKraus_hasSum (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K)
    (A : TraceClass H) : HasSum (fun k => conjugationLinearMap (K k) A)
      ((QuantumChannel.ofRectangularKraus K hK).toLinearMap A) :=
  rectangularKrausLinearMap_hasSum K hK A

/-- On a pure input, the output is the actual trace-norm convergent mixture
of the Kraus image vectors. No normalization of the individual vectors is required. -/
lemma QuantumChannel.ofRectangularKraus_vectorProjector_hasSum
    (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K) (x : H) :
    HasSum (fun k => vectorProjector (K k x))
      ((QuantumChannel.ofRectangularKraus K hK).toLinearMap (vectorProjector x)) := by
  simpa only [conjugationLinearMap_vectorProjector] using
    QuantumChannel.ofRectangularKraus_hasSum K hK (vectorProjector x)

lemma QuantumChannel.ofRectangularKraus_vectorProjector
    (K : ι → H →L[ℂ] J) (hK : RectangularKrausComplete K) (x : H) :
    (QuantumChannel.ofRectangularKraus K hK).toLinearMap (vectorProjector x) =
      ∑' k, vectorProjector (K k x) :=
  (QuantumChannel.ofRectangularKraus_vectorProjector_hasSum K hK x).tsum_eq.symm

end
end Cloning.InfiniteTraceClass
