import Cloning.PCTUnitaryTransportChannels
import Cloning.Main

/-! The physical cloning payoff and minimax values, optimizing over all actual
CPTP maps between the tensor registers. No limiting value enters a definition. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def statePayoff (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → A)) (Register (Fin m → A)))
    (ρ : Cloning.MatrixFidelity.State A) : ℝ :=
  ((tensorState ρ n).map Φ.toPositiveTracePreservingMap).rootFidelity (tensorState ρ m)

theorem statePayoff_nonneg (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → A)) (Register (Fin m → A)))
    (ρ : Cloning.MatrixFidelity.State A) : 0 ≤ statePayoff n m Φ ρ :=
  PositiveTraceClass.rootFidelity_nonneg _ _

theorem statePayoff_le_one (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → A)) (Register (Fin m → A)))
    (ρ : Cloning.MatrixFidelity.State A) : statePayoff n m Φ ρ ≤ 1 := by
  have h := PositiveTraceClass.rootFidelity_le_sqrt
    ((tensorState ρ n).map Φ.toPositiveTracePreservingMap) (tensorState ρ m)
  simpa only [statePayoff, PositiveTraceClass.norm_map, norm_tensorState, Real.sqrt_one,
    one_mul] using h

def orbitState {d : ℕ} (p : SimpleSpectrum (d+1))
    (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) : Cloning.MatrixFidelity.State (Fin (d+1)) :=
  conjugatedState (diagonalState p.eigenvalue (fun i ↦ (p.positive i).le) p.normalized) U

def spectrumPayoff {d : ℕ} (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (d+1))) (Register (Fin m → Fin (d+1))))
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) : ℝ :=
  statePayoff n m Φ (orbitState p U)

/-- Worst-case fidelity on the fixed-spectrum orbit, optimized over every
actual physical quantum channel. -/
def knownSpectrumValue {d : ℕ} (n m : ℕ) (p : SimpleSpectrum (d+1)) : ℝ :=
  LAN.minimaxValue (fun Φ U ↦ spectrumPayoff n m Φ p U)

/-- The spectral set is explicit; no closedness, interior or compactness is
silently built into the physical optimization problem. -/
def unknownSpectrumValue {d : ℕ} (n m : ℕ) (K : Set (SimpleSpectrum (d+1))) : ℝ :=
  LAN.minimaxValue (fun Φ (θ : K × unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) ↦
    spectrumPayoff n m Φ θ.1.val θ.2)

theorem spectrumPayoff_nonneg {d : ℕ} (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (d+1))) (Register (Fin m → Fin (d+1))))
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    0 ≤ spectrumPayoff n m Φ p U := statePayoff_nonneg _ _ _ _

theorem spectrumPayoff_le_one {d : ℕ} (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (d+1))) (Register (Fin m → Fin (d+1))))
    (p : SimpleSpectrum (d+1)) (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :
    spectrumPayoff n m Φ p U ≤ 1 := statePayoff_le_one _ _ _ _

end Cloning.TensorCloning
