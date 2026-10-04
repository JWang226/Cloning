import Cloning.PhysicalFlatGrassmannOrbit
import Cloning.PhysicalFlatCloningTheorem
import Cloning.WernerAsymptotics

/-! The sharp physical cloning theorem on the full Grassmann family of
literal rank-r orthogonal projectors, optimizing over all CPTP channels. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PhysicalFlatGrassmann
open Cloning.PCT Cloning.PCTPhysicalState Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
variable (r k : ℕ) (hr : 0 < r)
local instance : Nonempty (Fin (r+k)) := ⟨⟨0, Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
include hr

def payoff (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (r+k))) (Register (Fin m → Fin (r+k))))
    (P : Projector r k) : ℝ := by
  letI : Nonempty (Fin (r+k)) := ⟨⟨0, Nat.lt_of_lt_of_le hr (Nat.le_add_right r k)⟩⟩
  exact Cloning.TensorCloning.statePayoff n m Φ (state hr P)

/-- The adversary ranges over all actual rank-r orthogonal projectors. -/
def minimaxValue (n m : ℕ) : ℝ := LAN.minimaxValue (payoff r k hr n m)

theorem payoff_range_eq_orbit (n m : ℕ)
    (Φ : QuantumChannel (Register (Fin n → Fin (r+k))) (Register (Fin m → Fin (r+k)))) :
    Set.range (payoff r k hr n m Φ) =
      Set.range (Cloning.PhysicalFlatConverse.payoff r k hr n m Φ) := by
  ext x
  constructor
  · rintro ⟨P,rfl⟩
    obtain ⟨U,rfl⟩ := orbitProjector_surjective r k P
    refine ⟨U,?_⟩
    unfold payoff Cloning.PhysicalFlatConverse.payoff
    rw [state_orbitProjector]
  · rintro ⟨U,rfl⟩
    refine ⟨orbitProjector r k U,?_⟩
    unfold payoff Cloning.PhysicalFlatConverse.payoff
    rw [state_orbitProjector]

theorem minimaxValue_eq_orbit (n m : ℕ) :
    minimaxValue r k hr n m = Cloning.PhysicalFlatConverse.minimaxValue r k hr n m := by
  unfold minimaxValue Cloning.PhysicalFlatConverse.minimaxValue LAN.minimaxValue
  congr 1
  funext Φ
  change sInf (Set.range (payoff r k hr n m Φ)) =
    sInf (Set.range (Cloning.PhysicalFlatConverse.payoff r k hr n m Φ))
  rw [payoff_range_eq_orbit]

/-- Exact root fidelity optimized over all physical channels, uniformly
against every literal rank-r orthogonal projector in dimension r+k. -/
theorem minimaxValue_tendsto
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun n => minimaxValue r k hr n (m n)) atTop
      (𝓝 (γ ^ (-(((r*k : ℕ) : ℝ)/2)))) := by
  simpa only [minimaxValue_eq_orbit] using
    Cloning.PhysicalFlatConverse.minimaxValue_tendsto r k hr m γ hγ hratio

end Cloning.PhysicalFlatGrassmann
