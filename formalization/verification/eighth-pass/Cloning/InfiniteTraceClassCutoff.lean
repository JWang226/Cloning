import Cloning.InfiniteTraceClassChannels
import Cloning.InfiniteTraceClassSeries

/-! Projection compression with trace-preserving replacement on the actual
trace-class Banach space. The replacement state is explicit. -/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Multiplication by fixed bounded operators is continuous in trace norm. -/
def sandwichCLM (P Q : H →L[ℂ] H) : TraceClass H →L[ℂ] TraceClass H :=
  LinearMap.mkContinuous
    { toFun := fun A => TraceClass.ofOperator (P * A.1 * Q) (isTraceClass_mul_mul A.2)
      map_add' := by
        intro A B
        apply Subtype.ext
        change P * (A.1 + B.1) * Q = P * A.1 * Q + P * B.1 * Q
        simp [mul_add, add_mul]
      map_smul' := by
        intro c A
        apply Subtype.ext
        change P * (c • A.1) * Q = c • (P * A.1 * Q)
        simp }
    (‖P‖ * ‖Q‖) (fun A => by
      change traceNorm _ _ ≤ _ * traceNorm A.1 A.2
      calc
        traceNorm _ _ ≤ ‖P‖ * traceNorm A.1 A.2 * ‖Q‖ :=
          traceNorm_mul_mul_le A.2 _
        _ = _ := by ring)

@[simp] lemma sandwichCLM_coe (P Q : H →L[ℂ] H) (A : TraceClass H) :
    (sandwichCLM P Q A).1 = P * A.1 * Q := rfl

lemma sandwichCLM_nonneg {P : H →L[ℂ] H} (hP : IsSelfAdjoint P)
    (A : TraceClass H) (hA : 0 ≤ A.1) : 0 ≤ (sandwichCLM P P A).1 :=
  hP.conjugate_nonneg hA

/-- Trace cycling removes one copy of an orthogonal projection. -/
lemma traceCLM_sandwich_projection {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) :
    traceCLM (sandwichCLM P P A) = traceCLM (sandwichCLM 1 P A) := by
  have hAP : IsTraceClass (A.1 * P) := by
    simpa using (isTraceClass_mul_mul (A := 1) (B := P) A.2)
  have h := trace_mul_cycle (A := P) hAP
  have hleft : P * (A.1 * P) = P * A.1 * P := (mul_assoc _ _ _).symm
  have hright : A.1 * P * P = 1 * A.1 * P := by
    rw [mul_assoc, hP.isIdempotentElem.eq, one_mul]
  simpa only [hleft, hright] using h

/-- The two complementary compressed blocks have total trace equal to the input. -/
lemma traceCLM_projection_split {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (A : TraceClass H) :
    traceCLM (sandwichCLM P P A) + traceCLM (sandwichCLM (1 - P) (1 - P) A) =
      traceCLM A := by
  rw [traceCLM_sandwich_projection hP, traceCLM_sandwich_projection hP.one_sub,
    ← map_add]
  congr 1
  apply Subtype.ext
  change 1 * A.1 * P + 1 * A.1 * (1 - P) = A.1
  simp only [one_mul]
  rw [← mul_add, add_sub_cancel, mul_one]

/-- Projection compression followed by replacement of lost mass in `σ`.
This is linear on every trace-class input, including nonpositive inputs. -/
def projectionReplacement (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (σ : DensityState H) : PositiveTracePreservingMap H H where
  toLinearMap :=
    (sandwichCLM P P).toLinearMap +
      (traceCLM.comp (sandwichCLM (1 - P) (1 - P))).toLinearMap.smulRight
        (TraceClass.ofOperator σ.op σ.traceClass)
  map_nonneg := by
    intro A hA
    change 0 ≤ (sandwichCLM P P A).1 +
      traceCLM (sandwichCLM (1 - P) (1 - P) A) • σ.op
    have hQ := sandwichCLM_nonneg hP.one_sub.isSelfAdjoint A hA
    have ht := trace_eq_traceNorm_of_nonneg hQ (sandwichCLM (1 - P) (1 - P) A).2
    apply add_nonneg (sandwichCLM_nonneg hP.isSelfAdjoint A hA)
    change 0 ≤ trace (sandwichCLM (1 - P) (1 - P) A).1 _ • σ.op
    rw [ht]
    exact smul_nonneg (by exact_mod_cast traceNorm_nonneg _ _) σ.positive
  trace_preserving := by
    intro A
    change traceCLM ((sandwichCLM P P A) +
      traceCLM (sandwichCLM (1 - P) (1 - P) A) •
        TraceClass.ofOperator σ.op σ.traceClass) = traceCLM A
    rw [map_add, map_smul]
    change traceCLM (sandwichCLM P P A) +
      traceCLM (sandwichCLM (1 - P) (1 - P) A) * trace σ.op σ.traceClass = _
    rw [σ.trace_one, mul_one]
    exact traceCLM_projection_split hP A

lemma projectionReplacement_apply (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (σ : DensityState H) (A : TraceClass H) :
    projectionReplacement P hP σ A = sandwichCLM P P A +
      traceCLM (sandwichCLM (1 - P) (1 - P) A) •
        TraceClass.ofOperator σ.op σ.traceClass := rfl

/-- If the replacement state lies in the retained subspace, so does every output. -/
lemma projectionReplacement_supported (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (σ : DensityState H) (hσ : P * σ.op * P = σ.op) (A : TraceClass H) :
    P * (projectionReplacement P hP σ A).1 * P =
      (projectionReplacement P hP σ A).1 := by
  change P * (P * A.1 * P + _ • σ.op) * P = P * A.1 * P + _ • σ.op
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hσ]
  congr 1
  calc
    P * (P * A.1 * P) * P = (P * P) * A.1 * (P * P) := by simp only [mul_assoc]
    _ = P * A.1 * P := by rw [hP.isIdempotentElem.eq]

end
end Cloning.InfiniteTraceClass
