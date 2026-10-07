import Cloning.TensorLANEmbeddingAction

/-! Sector/Fock channels are defined for every finite input size. Before the
proved eventual cutoff basis exists, they prepare the fixed fallback state. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology Classical
open Filter
namespace Cloning.TensorLAN
open Cloning.PCT Cloning.TensorLie Cloning.InfiniteTraceClass
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def CutoffReady (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ) : Prop :=
  (∀ a : PositiveRoot d, 0 < rootGap mu a) ∧ LinearIndependent ℂ (cutoffRawFrame Ω mu R)

/-- A total sequence of actual forward channels, independent of an eventual
proof witness and defined on all finite sectors. -/
def sectorToFockTotal (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ) :
    QuantumChannel (cyclicSector Ω) (RootFock d) :=
  if h : CutoffReady Ω mu R then sectorToFock Ω mu R h.1 h.2 else
    QuantumChannel.ofContraction 0 (by intro x; simp)
      (DensityState.pure (rootVacuum d) (rootVacuum_norm d))

def fockToSectorTotal (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hΩ : ‖Ω‖ = 1) : QuantumChannel (RootFock d) (cyclicSector Ω) :=
  if h : CutoffReady Ω mu R then fockToSector Ω mu R hΩ h.1 h.2 else
    QuantumChannel.ofContraction 0 (by intro x; simp)
      (DensityState.pure ⟨Ω, highest_mem_cyclicSector Ω⟩ hΩ)

theorem sectorToFockTotal_eq (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (h : CutoffReady Ω mu R) : sectorToFockTotal Ω mu R = sectorToFock Ω mu R h.1 h.2 := by
  simp only [sectorToFockTotal, dif_pos h]

theorem fockToSectorTotal_eq (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hΩ : ‖Ω‖ = 1) (h : CutoffReady Ω mu R) :
    fockToSectorTotal Ω mu R hΩ = fockToSector Ω mu R hΩ h.1 h.2 := by
  simp only [fockToSectorTotal, dif_pos h]

/-- Actual gap divergence proves readiness of every fixed cutoff. -/
theorem partition_eventually_CutoffReady
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a) (R : ℕ) :
    ∀ᶠ N in atTop, CutoffReady (partitionHighestTensor (mu N) (hmu N)) (mu N) R := by
  have hli := partition_normalizedWord_eventually_linearIndependent
    (fun a : PositiveRoot d => a) Function.injective_id mu hmu δ hδ hgap
    (cutoffWord d R) (cutoffWord_perm_iff R)
  filter_upwards [hli, hgap, hδ.eventually (eventually_gt_atTop 0)] with N hN hg hp
  exact ⟨fun a => hp.trans_le (hg a), hN⟩

end Cloning.TensorLAN
