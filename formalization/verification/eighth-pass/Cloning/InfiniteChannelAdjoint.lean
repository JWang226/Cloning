import Cloning.InfiniteTraceClassChannels

/-!
# Adjoint preservation by positive maps on trace class

Positivity and complex linearity imply preservation of self-adjointness
and adjoints. These properties are proved from the Jordan and real/imaginary
decompositions, rather than added to the channel structure.
-/

namespace Cloning.InfiniteTraceClass

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace TraceClass

theorem realComponent_sub_I_smul_imaginaryComponent (A : TraceClass H) :
    realComponent A - Complex.I • imaginaryComponent A = adjoint A := by
  simp only [realComponent, imaginaryComponent, smul_smul]
  rw [show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
  module

end TraceClass

namespace PositiveTracePreservingMap

/-- A positive complex-linear map preserves the self-adjoint trace-class part. -/
theorem map_isSelfAdjoint (Φ : PositiveTracePreservingMap H K)
    (A : TraceClass H) (hA : IsSelfAdjoint A.1) : IsSelfAdjoint (Φ A).1 := by
  have hd : Φ A = Φ (TraceClass.positivePart A hA) -
      Φ (TraceClass.negativePart A hA) := by
    rw [← Φ.map_sub, TraceClass.positivePart_sub_negativePart]
  rw [hd]
  exact (IsSelfAdjoint.of_nonneg
    (Φ.map_nonneg _ (TraceClass.positivePart_nonneg A hA))).sub
    (IsSelfAdjoint.of_nonneg (Φ.map_nonneg _ (TraceClass.negativePart_nonneg A hA)))

/-- Adjoint preservation follows from positivity and complex linearity. -/
theorem map_adjoint (Φ : PositiveTracePreservingMap H K) (A : TraceClass H) :
    Φ (TraceClass.adjoint A) = TraceClass.adjoint (Φ A) := by
  have hr := Φ.map_isSelfAdjoint _ (TraceClass.realComponent_isSelfAdjoint A)
  have hi := Φ.map_isSelfAdjoint _ (TraceClass.imaginaryComponent_isSelfAdjoint A)
  have hsum : Φ A = Φ (TraceClass.realComponent A) +
      Complex.I • Φ (TraceClass.imaginaryComponent A) := by
    rw [← Φ.toLinearMap.map_smul, ← Φ.toLinearMap.map_add,
      TraceClass.realComponent_add_I_smul_imaginaryComponent]
  have hsub : Φ (TraceClass.adjoint A) = Φ (TraceClass.realComponent A) -
      Complex.I • Φ (TraceClass.imaginaryComponent A) := by
    rw [← Φ.toLinearMap.map_smul, ← Φ.map_sub,
      TraceClass.realComponent_sub_I_smul_imaginaryComponent]
  apply Subtype.ext
  change (Φ (TraceClass.adjoint A)).1 = star (Φ A).1
  rw [hsub, hsum]
  change (Φ (TraceClass.realComponent A)).1 -
      Complex.I • (Φ (TraceClass.imaginaryComponent A)).1 =
    star ((Φ (TraceClass.realComponent A)).1 +
      Complex.I • (Φ (TraceClass.imaginaryComponent A)).1)
  rw [star_add, star_smul, hr, hi]
  simp [sub_eq_add_neg]

end PositiveTracePreservingMap
end
end Cloning.InfiniteTraceClass
