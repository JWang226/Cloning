import Cloning.HeisenbergDual
import Cloning.WeylCovariantMultiplier
import Cloning.WeylMultimodeChannel

/-! The scalar Weyl multiplier now comes from an actual Schrödinger channel,
through its constructed normal Heisenberg adjoint. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Schrödinger covariance implies covariance of the reconstructed normal
Heisenberg dual, with the exact physical displacement conventions. -/
theorem heisenbergDual_weyl_covariance
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ T))
    (a : Fin d → ℂ) (A : Fock d →L[ℂ] Fock d) :
    ((displacement a).comp (heisenbergDual Φ A)).comp (displacement (-a)) =
      heisenbergDual Φ
        (((displacement (r • a)).comp A).comp (displacement (-(r • a)))) := by
  have hcov : ∀ T, Φ (sandwichCLM (displacement (-a))
      (star (displacement (-a))) T) =
      sandwichCLM (displacement (r • (-a)))
        (star (displacement (r • (-a)))) (Φ T) := by
    intro T
    simpa only [displacementTraceMap, ContinuousLinearMap.star_eq_adjoint,
      displacement_adjoint] using hΦ (-a) T
  have h := heisenbergDual_covariance Φ (displacement (-a))
    (displacement (r • (-a))) hcov A
  simpa only [ContinuousLinearMap.star_eq_adjoint, displacement_adjoint,
    neg_neg, smul_neg, ContinuousLinearMap.mul_def] using h

/-- The Weyl multiplier representation for a genuine bounded covariant
trace-class map. Irreducibility and the normal dual are both constructed. -/
theorem traceClass_covariant_weyl_multiplier
    (Φ : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ T)) (b : Fin d → ℂ) :
    heisenbergDual Φ (displacement b) =
      weylMultiplier (heisenbergDual Φ) r b • displacement (r • b) :=
  covariant_linearMap_weyl_multiplier (heisenbergDual Φ) r
    (heisenbergDual_weyl_covariance Φ r hΦ) b

/-- Every actual Weyl-covariant CPTP channel has a normalized scalar Weyl
multiplier for its actual normal Heisenberg adjoint. -/
theorem quantumChannel_weyl_multiplier
    (Φ : QuantumChannel (Fock d) (Fock d)) (r : ℝ)
    (hΦ : ∀ a T, Φ.toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (r • a) (Φ.toLinearMap T)) :
    (∀ b, Φ.heisenberg (displacement b) =
      weylMultiplier Φ.heisenberg r b • displacement (r • b)) ∧
      weylMultiplier Φ.heisenberg r 0 = 1 := by
  constructor
  · exact traceClass_covariant_weyl_multiplier
      Φ.toPositiveTracePreservingMap.toContinuousLinearMap r hΦ
  · exact weylMultiplier_zero Φ.heisenberg r Φ.heisenberg_unital

end Cloning.MultimodeCoherent
