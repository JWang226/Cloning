import Cloning.TensorGibbsDisplacedTransfer
import Cloning.TensorGibbsThermalIdentification
import Cloning.TensorLANEmbeddingTotal

/-! The concrete sector/Fock maps compare displaced Gibbs and product thermal
states using derived spectral tails and literal vector compression errors. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.TensorLAN
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

def sectorFockTransport (Q : ℕ) (hq : CutoffReady Ω mu Q) : cyclicSector Ω →L[ℂ] RootFock d :=
  frameTransport (sectorCutoff Ω Q) (sectorCutoffBasis Ω mu Q hq.1 hq.2)
    (cutoffNumberFrame d Q) (cutoffNumberFrame_orthonormal d Q)

theorem sectorFockTransport_contraction (Q : ℕ) (hq : CutoffReady Ω mu Q) (x : cyclicSector Ω) :
    ‖sectorFockTransport Ω mu Q hq x‖ ≤ ‖x‖ := frameTransport_contraction _ _ _ _ x

theorem sectorFockTransport_adjoint_contraction (Q : ℕ) (hq : CutoffReady Ω mu Q) (x : RootFock d) :
    ‖(sectorFockTransport Ω mu Q hq).adjoint x‖ ≤ ‖x‖ := frameTransport_adjoint_contraction _ _ _ _ x

theorem sectorToFockTotal_displaced_gibbs_error (hΩ : ‖Ω‖ = 1)
    (p t : Fin d → ℝ) (hp : ∀ a, 0 < p a) (ht : ∀ a, 0 < t a) (htord : StrictAnti t)
    (R Q : ℕ) (hr : CutoffReady Ω mu R) (hq : CutoffReady Ω mu Q)
    (U : cyclicSector Ω →ₗᵢ[ℂ] cyclicSector Ω) (W : RootFock d →ₗᵢ[ℂ] RootFock d) :
    ‖(sectorToFockTotal Ω mu Q).toLinearMap
        ((QuantumChannel.ofIsometry U).toLinearMap (sectorGibbsDensity Ω mu hweight hraise p)) -
      (QuantumChannel.ofIsometry W).toLinearMap (rootThermalState t)‖ ≤
      gibbsThermalCutoffError Ω mu hweight hraise p t R +
      4 * ∑ i : CutoffIndex d R, bosonicOccupationWeight t (cutoffOccupation d R i).val *
        ‖sectorFockTransport Ω mu Q hq (U (cutoffSectorFrame Ω mu R i)) - W (cutoffNumberFrame d R i)‖ := by
  rw [sectorToFockTotal_eq Ω mu Q hq]
  have hh := displaced_mixture_channel_error (sectorFockTransport Ω mu Q hq)
    (sectorFockTransport_contraction Ω mu Q hq) (DensityState.pure (rootVacuum d) (rootVacuum_norm d)) U W
    (sectorGibbsDensity Ω mu hweight hraise p) (sectorGibbsDensity_nonneg Ω mu hweight hraise hΩ p hp)
    (rootThermalState t) (rootThermalState_nonneg t ht htord)
    (cutoffSectorFrame Ω mu R) (cutoffNumberFrame d R)
    (cutoffSectorFrame_orthonormal Ω mu R hr.2).norm_eq_one (cutoffNumberFrame_orthonormal d R).norm_eq_one
    (fun i => sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val)
    (fun i => bosonicOccupationWeight t (cutoffOccupation d R i).val)
    (fun i => bosonicOccupationWeight_nonneg t ht htord _)
  change _ ≤ _ at hh
  unfold gibbsThermalCutoffError gibbsThermalCoefficientError
  dsimp only [sectorGibbsCutoff, rootThermalCutoff]
  convert hh using 1 <;> try rfl
  ring

theorem fockToSectorTotal_displaced_gibbs_error (hΩ : ‖Ω‖ = 1)
    (p t : Fin d → ℝ) (hp : ∀ a, 0 < p a) (ht : ∀ a, 0 < t a) (htord : StrictAnti t)
    (R Q : ℕ) (hr : CutoffReady Ω mu R) (hq : CutoffReady Ω mu Q)
    (U : cyclicSector Ω →ₗᵢ[ℂ] cyclicSector Ω) (W : RootFock d →ₗᵢ[ℂ] RootFock d) :
    ‖(fockToSectorTotal Ω mu Q hΩ).toLinearMap
        ((QuantumChannel.ofIsometry W).toLinearMap (rootThermalState t)) -
      (QuantumChannel.ofIsometry U).toLinearMap (sectorGibbsDensity Ω mu hweight hraise p)‖ ≤
      gibbsThermalCutoffError Ω mu hweight hraise p t R +
      4 * ∑ i : CutoffIndex d R, sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val *
        ‖(sectorFockTransport Ω mu Q hq).adjoint (W (cutoffNumberFrame d R i)) - U (cutoffSectorFrame Ω mu R i)‖ := by
  rw [fockToSectorTotal_eq Ω mu Q hΩ hq]
  have hh := displaced_mixture_channel_error (sectorFockTransport Ω mu Q hq).adjoint
    (sectorFockTransport_adjoint_contraction Ω mu Q hq)
    (DensityState.pure ⟨Ω, highest_mem_cyclicSector Ω⟩ hΩ) W U
    (rootThermalState t) (rootThermalState_nonneg t ht htord)
    (sectorGibbsDensity Ω mu hweight hraise p) (sectorGibbsDensity_nonneg Ω mu hweight hraise hΩ p hp)
    (cutoffNumberFrame d R) (cutoffSectorFrame Ω mu R)
    (cutoffNumberFrame_orthonormal d R).norm_eq_one (cutoffSectorFrame_orthonormal Ω mu R hr.2).norm_eq_one
    (fun i => bosonicOccupationWeight t (cutoffOccupation d R i).val)
    (fun i => sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val)
    (fun i => sectorOccupationWeight_nonneg Ω mu hweight hraise hΩ p hp _)
  simp only [abs_sub_comm (bosonicOccupationWeight t _)] at hh
  unfold gibbsThermalCutoffError gibbsThermalCoefficientError
  dsimp only [sectorGibbsCutoff, rootThermalCutoff]
  convert hh using 1 <;> try rfl
  ring

end Cloning.TensorLie
