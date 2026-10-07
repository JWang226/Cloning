import Cloning.MultimodeIdlerCharacteristicCovariance
import Cloning.MultimodeIdlerCharacteristicMultiplier

/-! Exact characteristic function of the actual multimode seeded idler map.
The negative phase-conjugated frequency is derived from its positive
negative-binomial columns, rather than imposed as a representation premise. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeIdler
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Every complex trace-class input of the literal negative-binomial channel
obeys the quantum-limited phase-conjugating characteristic formula. -/
theorem channel_characteristic (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (A : TraceClass (Fock d)) (a : Fin d → ℂ) :
    tracePairing ((channel q (fun i => (hq0 i).le) hq1).toLinearMap A) (displacement a) =
      (∏ i, (Real.exp (-‖a i‖^2/(2*(1-q i))) : ℂ)) *
        tracePairing A (displacement (-(diagonalScale
          (fun i => Real.sqrt (q i)/Real.sqrt (1-q i)) (star a)))) := by
  apply quantumChannel_conjugateScale_characteristic _ q _ hq0 hq1
  · intro i
    rw [div_pow, Real.sq_sqrt (hq0 i).le, Real.sq_sqrt (sub_nonneg.mpr (hq1 i).le)]
  · intro z T
    simpa only [diagonalScale, complementaryScale, div_eq_mul_inv] using
      channel_weyl_covariant q (fun i => (hq0 i).le) hq1 z T
  · exact channel_vacuum q (fun i => (hq0 i).le) hq1

end Cloning.MultimodeIdler
