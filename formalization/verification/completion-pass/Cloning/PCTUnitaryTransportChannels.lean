import Cloning.PCTUnitaryTransport

/-! Actual channel transport of arbitrary tensor states and complete physical
frames, with exact inverse identities on every trace-class input. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Topology
open MeasureTheory Cloning.InfiniteTraceClass Cloning.Hybrid
namespace Cloning.PCTUnitaryTransport
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTPurificationChannel
open Cloning.PCTPhysicalState
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def conjugatedState (ρ : Cloning.MatrixFidelity.State A) (U : unitary (Matrix A A ℂ)) :
    Cloning.MatrixFidelity.State A where
  matrix := (U : Matrix A A ℂ) * ρ.matrix * (U : Matrix A A ℂ)ᴴ
  positive := ρ.positive.mul_mul_conjTranspose_same _
  trace_one := by
    have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, ρ.trace_one]

theorem unitaryChannel_star (U : unitary (Matrix A A ℂ)) (X : TraceClass (Register A)) :
    (unitaryChannel (star U)).toLinearMap ((unitaryChannel U).toLinearMap X) = X := by
  rw [← Cloning.PCTGlobal.registerLiftCLM_matrixOf X, unitaryChannel_registerLift,
    unitaryChannel_registerLift]
  have hU : (U : Matrix A A ℂ)ᴴ * U = 1 := Unitary.star_mul_self_of_mem U.property
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc]
  rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]

theorem unitaryChannel_star_right (U : unitary (Matrix A A ℂ)) (X : TraceClass (Register A)) :
    (unitaryChannel U).toLinearMap ((unitaryChannel (star U)).toLinearMap X) = X := by
  simpa only [star_star] using unitaryChannel_star (star U) X

@[simp] theorem tensorUnitary_star (U : unitary (Matrix A A ℂ)) (L : ℕ) :
    tensorUnitary (star U) L = star (tensorUnitary U L) := by
  apply Subtype.ext
  simp only [tensorUnitary, Unitary.coe_star, Matrix.star_eq_conjTranspose, tensorPower_star]

theorem tensorState_conjugated (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) (L : ℕ) :
    (unitaryChannel (tensorUnitary U L)).toLinearMap (tensorState ρ L).1 =
      (tensorState (conjugatedState ρ U) L).1 :=
  tensor_unitaryChannel_matrixTensorPower U ρ.matrix L

theorem tensorState_conjugated_inverse (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) (L : ℕ) :
    (unitaryChannel (tensorUnitary (star U) L)).toLinearMap
      (tensorState (conjugatedState ρ U) L).1 = (tensorState ρ L).1 := by
  rw [← tensorState_conjugated, tensorUnitary_star, unitaryChannel_star]

theorem frameState_transport {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (U : unitary (Matrix A A ℂ)) (z : Fin s → ℂ) (L : ℕ) :
    (unitaryChannel (tensorUnitary U L)).toLinearMap (frameState u z L).1 =
      (frameState (transportFrame u U) z L).1 := by
  rw [frameState_val, frameState_val, reduced_frameParticle_transport,
    tensor_unitaryChannel_matrixTensorPower]

theorem frameState_transport_inverse {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (U : unitary (Matrix A A ℂ)) (z : Fin s → ℂ) (L : ℕ) :
    (unitaryChannel (tensorUnitary (star U) L)).toLinearMap
      (frameState (transportFrame u U) z L).1 = (frameState u z L).1 := by
  rw [← frameState_transport, tensorUnitary_star, unitaryChannel_star]

theorem transportFrame_canonical_zero {s : ℕ}
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A × A)))
    (ρ : Cloning.MatrixFidelity.State A) (U : unitary (Matrix A A ℂ))
    (hu : u 0 = canonicalPurification (conjugatedState ρ U).matrix) :
    transportFrame u (star U) 0 = canonicalPurification ρ.matrix := by
  change conjugatePurification (star U) (u 0) = _
  rw [hu]
  change conjugatePurification (star U)
    (canonicalPurification ((U : Matrix A A ℂ) * ρ.matrix * (U : Matrix A A ℂ)ᴴ)) = _
  rw [canonicalPurification_conjugate U ρ.matrix ρ.positive]
  exact conjugatePurification_star U _

/-- Postcompose a reverse mixed channel with an actual quantum channel. -/
def postQuantum {Ω H K J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (M : QuantumChannel K J) (S : HybridToQuantum H K μ) : HybridToQuantum H J μ where
  map := M.toPositiveTracePreservingMap.toContinuousLinearMap.comp S.map
  completelyPositive := fun n X hX => M.completelyPositive n _ (S.completelyPositive n X hX)
  tracePreserving := fun X => (M.trace_preserving (S.map X)).trans (S.tracePreserving X)

@[simp] theorem postQuantum_apply {Ω H K J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (M : QuantumChannel K J) (S : HybridToQuantum H K μ)
    (X : Lp (TraceClass H) 1 μ) : (postQuantum M S).map X = M.toLinearMap (S.map X) := rfl

end Cloning.PCTUnitaryTransport
