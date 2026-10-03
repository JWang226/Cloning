import Cloning.InfiniteTraceClassAlgebra
import Cloning.InfiniteTraceClassPositive
import Cloning.InfiniteDensityState

/-! Positive trace-preserving maps on the genuine trace-class Banach space.
The trace-norm contraction below is proved from the CFC Jordan decomposition;
it is not a field of the map structure. Complete positivity is unnecessary for
this particular contraction theorem. -/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder InnerProductSpace

variable {H K J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

namespace TraceClass

/-- The positive Jordan part, as an actual trace-class operator. -/
def positivePart (A : TraceClass H) (hA : IsSelfAdjoint A.1) : TraceClass H :=
  ofOperator A.1⁺ (isTraceClass_posPart_of_isSelfAdjoint hA A.2)

/-- The negative Jordan part, as an actual trace-class operator. -/
def negativePart (A : TraceClass H) (hA : IsSelfAdjoint A.1) : TraceClass H :=
  ofOperator A.1⁻ (isTraceClass_negPart_of_isSelfAdjoint hA A.2)

lemma positivePart_nonneg (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    0 ≤ (positivePart A hA).1 := CFC.posPart_nonneg A.1

lemma negativePart_nonneg (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    0 ≤ (negativePart A hA).1 := CFC.negPart_nonneg A.1

lemma positivePart_sub_negativePart (A : TraceClass H) (hA : IsSelfAdjoint A.1) :
    positivePart A hA - negativePart A hA = A := by
  apply Subtype.ext
  exact CFC.posPart_sub_negPart A.1 hA

/-- The exact mass identity for the Jordan decomposition in trace norm. -/
lemma norm_positivePart_add_norm_negativePart (A : TraceClass H)
    (hA : IsSelfAdjoint A.1) :
    ‖positivePart A hA‖ + ‖negativePart A hA‖ = ‖A‖ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hp := summable_inner_abs_of_hilbertBasis (positivePart A hA).2 b
  have hn := summable_inner_abs_of_hilbertBasis (negativePart A hA).2 b
  simp only [norm_eq_traceNorm]
  rw [traceNorm_eq_of_hilbertBasis _ b, traceNorm_eq_of_hilbertBasis _ b,
    traceNorm_eq_of_hilbertBasis _ b]
  rw [← hp.tsum_add hn]
  apply tsum_congr
  intro i
  change (⟪b i, CFC.abs A.1⁺ (b i)⟫_ℂ).re +
    (⟪b i, CFC.abs A.1⁻ (b i)⟫_ℂ).re = _
  rw [CFC.abs_of_nonneg _ (CFC.posPart_nonneg _),
    CFC.abs_of_nonneg _ (CFC.negPart_nonneg _), ← Complex.add_re,
    ← inner_add_right, ← ContinuousLinearMap.add_apply,
    CFC.posPart_add_negPart A.1 hA]

lemma norm_eq_trace_re_of_nonneg (A : TraceClass H) (hA : 0 ≤ A.1) :
    ‖A‖ = (trace A.1 A.2).re :=
  (trace_re_eq_traceNorm hA A.2).symm

/-- The adjoint remains trace class. -/
def adjoint (A : TraceClass H) : TraceClass H :=
  ofOperator (star A.1) (isTraceClass_star A.2)

lemma norm_adjoint (A : TraceClass H) : ‖adjoint A‖ = ‖A‖ :=
  traceNorm_star A.2

/-- The real self-adjoint component of a trace-class operator. -/
def realComponent (A : TraceClass H) : TraceClass H :=
  (1 / 2 : ℂ) • (A + adjoint A)

/-- The imaginary self-adjoint component of a trace-class operator. -/
def imaginaryComponent (A : TraceClass H) : TraceClass H :=
  (-Complex.I / 2 : ℂ) • (A - adjoint A)

lemma realComponent_isSelfAdjoint (A : TraceClass H) :
    IsSelfAdjoint (realComponent A).1 := by
  change star ((1 / 2 : ℂ) • (A.1 + star A.1)) = (1 / 2 : ℂ) • (A.1 + star A.1)
  simp [star_smul, star_add, add_comm]

lemma imaginaryComponent_isSelfAdjoint (A : TraceClass H) :
    IsSelfAdjoint (imaginaryComponent A).1 := by
  change star ((-Complex.I / 2 : ℂ) • (A.1 - star A.1)) =
    (-Complex.I / 2 : ℂ) • (A.1 - star A.1)
  simp only [star_smul, star_sub, star_star]
  rw [show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]
  rw [show star A.1 - A.1 = -(A.1 - star A.1) by abel, smul_neg]
  rw [neg_div, neg_smul]

lemma realComponent_add_I_smul_imaginaryComponent (A : TraceClass H) :
    realComponent A + Complex.I • imaginaryComponent A = A := by
  simp only [realComponent, imaginaryComponent, smul_smul]
  rw [show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
  rw [← smul_add]
  module

lemma norm_realComponent_le (A : TraceClass H) : ‖realComponent A‖ ≤ ‖A‖ := by
  calc
    ‖realComponent A‖ = (1 / 2 : ℝ) * ‖A + adjoint A‖ := by
      rw [realComponent, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖adjoint A‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖A‖ := by rw [norm_adjoint]; ring

lemma norm_imaginaryComponent_le (A : TraceClass H) : ‖imaginaryComponent A‖ ≤ ‖A‖ := by
  calc
    ‖imaginaryComponent A‖ = (1 / 2 : ℝ) * ‖A - adjoint A‖ := by
      rw [imaginaryComponent, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖adjoint A‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = ‖A‖ := by rw [norm_adjoint]; ring

end TraceClass

/-- A positive trace-preserving complex-linear map on the trace-class Banach spaces.
No contractivity or continuity is assumed in this definition. -/
structure PositiveTracePreservingMap
    (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  toLinearMap : TraceClass H →ₗ[ℂ] TraceClass K
  map_nonneg : ∀ A, 0 ≤ A.1 → 0 ≤ (toLinearMap A).1
  trace_preserving : ∀ A,
    trace (toLinearMap A).1 (toLinearMap A).2 = trace A.1 A.2

namespace PositiveTracePreservingMap

instance instCoeFun : CoeFun (PositiveTracePreservingMap H K)
    (fun _ => TraceClass H → TraceClass K) := ⟨fun Φ => Φ.toLinearMap⟩

@[simp] lemma map_sub (Φ : PositiveTracePreservingMap H K) (A B : TraceClass H) :
    Φ (A - B) = Φ A - Φ B := Φ.toLinearMap.map_sub A B

/-- A positive input retains its exact trace norm under a positive TP map. -/
lemma norm_map_of_nonneg (Φ : PositiveTracePreservingMap H K)
    (A : TraceClass H) (hA : 0 ≤ A.1) : ‖Φ A‖ = ‖A‖ := by
  rw [TraceClass.norm_eq_trace_re_of_nonneg _ (Φ.map_nonneg A hA),
    Φ.trace_preserving, TraceClass.norm_eq_trace_re_of_nonneg _ hA]

/-- Trace-norm contraction on every self-adjoint trace-class input. -/
theorem norm_map_le_of_isSelfAdjoint (Φ : PositiveTracePreservingMap H K)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) : ‖Φ A‖ ≤ ‖A‖ := by
  have hd := TraceClass.positivePart_sub_negativePart A hA
  calc
    ‖Φ A‖ = ‖Φ (TraceClass.positivePart A hA) -
        Φ (TraceClass.negativePart A hA)‖ := by rw [← Φ.map_sub, hd]
    _ ≤ ‖Φ (TraceClass.positivePart A hA)‖ +
        ‖Φ (TraceClass.negativePart A hA)‖ := norm_sub_le _ _
    _ = ‖TraceClass.positivePart A hA‖ + ‖TraceClass.negativePart A hA‖ := by
      rw [Φ.norm_map_of_nonneg _ (TraceClass.positivePart_nonneg A hA),
        Φ.norm_map_of_nonneg _ (TraceClass.negativePart_nonneg A hA)]
    _ = ‖A‖ := TraceClass.norm_positivePart_add_norm_negativePart A hA

/-- In particular, differences of positive states contract in the genuine trace norm. -/
theorem norm_map_sub_le (Φ : PositiveTracePreservingMap H K)
    (A B : TraceClass H) (hA : 0 ≤ A.1) (hB : 0 ≤ B.1) :
    ‖Φ A - Φ B‖ ≤ ‖A - B‖ := by
  rw [← Φ.map_sub]
  exact Φ.norm_map_le_of_isSelfAdjoint (A - B)
    ((IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB))

/-- Positivity and trace preservation already force boundedness on the whole
complex trace-class space; no continuity assumption is needed. -/
theorem norm_map_le_two_mul (Φ : PositiveTracePreservingMap H K) (A : TraceClass H) :
    ‖Φ A‖ ≤ 2 * ‖A‖ := by
  have hd := TraceClass.realComponent_add_I_smul_imaginaryComponent A
  calc
    ‖Φ A‖ = ‖Φ (TraceClass.realComponent A) +
        Complex.I • Φ (TraceClass.imaginaryComponent A)‖ := by
      conv_lhs => rw [← hd]
      rw [Φ.toLinearMap.map_add, Φ.toLinearMap.map_smul]
    _ ≤ ‖Φ (TraceClass.realComponent A)‖ +
        ‖Complex.I • Φ (TraceClass.imaginaryComponent A)‖ := norm_add_le _ _
    _ = ‖Φ (TraceClass.realComponent A)‖ + ‖Φ (TraceClass.imaginaryComponent A)‖ := by
      simp [norm_smul]
    _ ≤ ‖TraceClass.realComponent A‖ + ‖TraceClass.imaginaryComponent A‖ :=
      add_le_add
        (Φ.norm_map_le_of_isSelfAdjoint _ (TraceClass.realComponent_isSelfAdjoint A))
        (Φ.norm_map_le_of_isSelfAdjoint _ (TraceClass.imaginaryComponent_isSelfAdjoint A))
    _ ≤ ‖A‖ + ‖A‖ := add_le_add (TraceClass.norm_realComponent_le A)
      (TraceClass.norm_imaginaryComponent_le A)
    _ = 2 * ‖A‖ := by ring

/-- The continuous linear map derived from positivity and trace preservation. -/
def toContinuousLinearMap (Φ : PositiveTracePreservingMap H K) :
    TraceClass H →L[ℂ] TraceClass K :=
  Φ.toLinearMap.mkContinuous 2 Φ.norm_map_le_two_mul

lemma continuous (Φ : PositiveTracePreservingMap H K) : Continuous Φ :=
  Φ.toContinuousLinearMap.continuous

/-- The image of a density operator is a density operator. -/
def mapState (Φ : PositiveTracePreservingMap H K) (ρ : DensityState H) : DensityState K where
  op := (Φ (TraceClass.ofOperator ρ.op ρ.traceClass)).1
  positive := Φ.map_nonneg _ ρ.positive
  traceClass := (Φ (TraceClass.ofOperator ρ.op ρ.traceClass)).2
  trace_one := (Φ.trace_preserving _).trans ρ.trace_one

/-- Identity on trace-class operators. -/
def id : PositiveTracePreservingMap H H where
  toLinearMap := LinearMap.id
  map_nonneg := fun _ h => h
  trace_preserving := fun _ => rfl

/-- Composition preserves positivity and trace preservation. -/
def comp (Ψ : PositiveTracePreservingMap K J) (Φ : PositiveTracePreservingMap H K) :
    PositiveTracePreservingMap H J where
  toLinearMap := Ψ.toLinearMap.comp Φ.toLinearMap
  map_nonneg := fun A hA => Ψ.map_nonneg _ (Φ.map_nonneg A hA)
  trace_preserving := fun A => (Ψ.trace_preserving _).trans (Φ.trace_preserving A)

end PositiveTracePreservingMap
end
end Cloning.InfiniteTraceClass
