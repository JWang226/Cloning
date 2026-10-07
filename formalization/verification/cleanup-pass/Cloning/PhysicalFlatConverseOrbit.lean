import Cloning.TensorFlatProjectorRankLaw
import Cloning.TensorCloningPayoff

/-! The literal rank-r flat-state unitary orbit and its all-channel physical
cloning minimax value. -/
noncomputable section
open scoped BigOperators
namespace Cloning.PhysicalFlatConverse
open Cloning.PCT Cloning.TensorLie Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable (r k : ℕ) (hr : 0 < r)
local instance : Nonempty (Fin (r+k)) := ⟨⟨0, Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
include hr

def flatState : Cloning.MatrixFidelity.State (Fin (r+k)) :=
  diagonalState (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) (TensorLie.rankFlatSpectrum_sum hr)

def orbitState (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    Cloning.MatrixFidelity.State (Fin (r+k)) := conjugatedState (flatState r k hr) U

def payoff (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (r+k))) (Register (Fin m → Fin (r+k))))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) : ℝ := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0, Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  exact TensorCloning.statePayoff n m Φ (orbitState r k hr U)

def minimaxValue (n m : ℕ) : ℝ := LAN.minimaxValue (payoff r k hr n m)

theorem payoff_nonneg (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (r+k))) (Register (Fin m → Fin (r+k))))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) : 0 ≤ payoff r k hr n m Φ U := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0, Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  exact TensorCloning.statePayoff_nonneg _ _ _ _

theorem payoff_le_one (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (r+k))) (Register (Fin m → Fin (r+k))))
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) : payoff r k hr n m Φ U ≤ 1 := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0, Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  exact TensorCloning.statePayoff_le_one _ _ _ _

end Cloning.PhysicalFlatConverse
