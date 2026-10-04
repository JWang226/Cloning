import Cloning.TensorCloningGlobalCovariance
import Cloning.TensorCloningSectorCovariance
import Cloning.PCTUnitaryTransportChannels

/-! Exact independence of both prescribed physical channel payoffs from
the unknown unitary eigenbasis, at every finite sample size. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport Cloning.FiniteKrausLift Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

private theorem state_eq_of_matrix_eq {A : Type*} [Fintype A]
    (ρ σ : Cloning.MatrixFidelity.State A) (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem tensor_unitaryChannel_eq_conjugation {d : ℕ} [Nonempty (Fin d)]
    (n : ℕ) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : TraceClass (TensorRegister n (Fin d))) :
    (unitaryChannel (tensorUnitary U n)).toLinearMap A = conjugationLinearMap (tensorOperator n U) A := by
  have he : matrixRegister (tensorPower n U.val) = tensorOperator n U.val := by
    apply ContinuousLinearMap.ext
    intro x
    ext w
    simp only [matrixRegister_apply, tensorOperator_apply, tensorPower]
  rw [← Cloning.PCTGlobal.registerLiftCLM_matrixOf A, unitaryChannel_registerLift,
    ← he, conjugation_matrixRegister]
  rfl

theorem rootFidelity_unitaryChannel {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (U : unitary (Matrix A A ℂ)) (ρ σ : PositiveTraceClass (Register A)) :
    (ρ.map (unitaryChannel U).toPositiveTracePreservingMap).rootFidelity
      (σ.map (unitaryChannel U).toPositiveTracePreservingMap) = ρ.rootFidelity σ := by
  have hρ : (ρ.map (unitaryChannel U).toPositiveTracePreservingMap).map
      (unitaryChannel (star U)).toPositiveTracePreservingMap = ρ := Subtype.ext (unitaryChannel_star U ρ.1)
  have hσ : (σ.map (unitaryChannel U).toPositiveTracePreservingMap).map
      (unitaryChannel (star U)).toPositiveTracePreservingMap = σ := Subtype.ext (unitaryChannel_star U σ.1)
  apply le_antisymm
  · have h := InfiniteFidelity.fidelity_data_processing (unitaryChannel (star U))
      (ρ.map (unitaryChannel U).toPositiveTracePreservingMap).1
      (σ.map (unitaryChannel U).toPositiveTracePreservingMap).1
      (ρ.map (unitaryChannel U).toPositiveTracePreservingMap).2
      (σ.map (unitaryChannel U).toPositiveTracePreservingMap).2
    change _ ≤ ((ρ.map _).map _).rootFidelity ((σ.map _).map _) at h
    simpa only [hρ,hσ] using h
  · exact InfiniteFidelity.fidelity_data_processing (unitaryChannel U) ρ.1 σ.1 ρ.2 σ.2

theorem spectrumPayoff_unitary_of_covariant {d : ℕ} (n m : ℕ)
    (Φ : QuantumChannel (TensorRegister n (Fin (d+1))) (TensorRegister m (Fin (d+1))))
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
    (hcov : ∀ A, Φ.toLinearMap (conjugationLinearMap (tensorOperator n U) A) =
      conjugationLinearMap (tensorOperator m U) (Φ.toLinearMap A)) :
    spectrumPayoff n m Φ p U = spectrumPayoff n m Φ p 1 := by
  let ρ := diagonalState p.eigenvalue (fun a => (p.positive a).le) p.normalized
  let A := (tensorState ρ n).map Φ.toPositiveTracePreservingMap
  let B := tensorState ρ m
  have hA : (tensorState (orbitState p U) n).map Φ.toPositiveTracePreservingMap =
      A.map (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap := by
    apply Subtype.ext
    change Φ.toLinearMap (tensorState (conjugatedState ρ U) n).1 = _
    rw [← tensorState_conjugated, tensor_unitaryChannel_eq_conjugation,
      hcov, ← tensor_unitaryChannel_eq_conjugation]
    rfl
  have hB : tensorState (orbitState p U) m = B.map (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap :=
    Subtype.ext (tensorState_conjugated ρ U m).symm
  have hρ : orbitState p (1 : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) = ρ := by
    have he : (orbitState p (1 : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))).matrix = ρ.matrix := by
      simp [orbitState, conjugatedState, ρ, diagonalState]
    exact state_eq_of_matrix_eq _ _ he
  change ((tensorState (orbitState p U) n).map Φ.toPositiveTracePreservingMap).rootFidelity
    (tensorState (orbitState p U) m) = _
  rw [hA,hB,rootFidelity_unitaryChannel]
  change _ = ((tensorState (orbitState p 1) n).map Φ.toPositiveTracePreservingMap).rootFidelity
    (tensorState (orbitState p 1) m)
  rw [hρ]

theorem knownSpectrumChannel_payoff_unitary {d : ℕ} (n m : ℕ) (p : SimpleSpectrum (d+1))
    (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    spectrumPayoff n m (knownSpectrumChannel n m (d+1) p.eigenvalue
      (fun a => (p.positive a).le) p.normalized) p U =
    spectrumPayoff n m (knownSpectrumChannel n m (d+1) p.eigenvalue
      (fun a => (p.positive a).le) p.normalized) p 1 :=
  spectrumPayoff_unitary_of_covariant n m _ p U
    (knownSpectrumChannel_covariant n m (d+1) p.eigenvalue (fun a => (p.positive a).le) p.normalized U
      (Unitary.star_mul_self_of_mem U.property))

theorem universalChannel_payoff_unitary {d : ℕ} (n m : ℕ) (p : SimpleSpectrum (d+1))
    (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    spectrumPayoff n m (universalChannel n m d) p U = spectrumPayoff n m (universalChannel n m d) p 1 :=
  spectrumPayoff_unitary_of_covariant n m _ p U
    (universalChannel_covariant n m d U (Unitary.star_mul_self_of_mem U.property))

end Cloning.TensorCloning
