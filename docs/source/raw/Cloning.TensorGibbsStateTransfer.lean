import Cloning.TensorGibbsThermalCutoff
import Cloning.TensorLANEmbeddingTotal

/-! Concrete two-sided centered Gibbs/thermal comparison through the actual
sector/Fock channels, with explicit finite-cutoff error. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.TensorLAN
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

def gibbsThermalCoefficientError (p t : Fin d → ℝ) (R : ℕ) : ℝ :=
  ∑ i : CutoffIndex d R, |sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val -
    bosonicOccupationWeight t (cutoffOccupation d R i).val|

def gibbsThermalCutoffError (p t : Fin d → ℝ) (R : ℕ) : ℝ :=
  ‖sectorGibbsDensity Ω mu hweight hraise p - sectorGibbsCutoff Ω mu hweight hraise p R‖ +
  gibbsThermalCoefficientError Ω mu hweight hraise p t R +
  ‖rootThermalState t - rootThermalCutoff t R‖

theorem sectorOccupationWeight_nonneg (hΩ : ‖Ω‖ = 1) (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (k : PositiveRoot d → ℕ) :
    0 ≤ sectorOccupationWeight Ω mu hweight hraise p k :=
  mul_nonneg (div_nonneg (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a).le _))
    (sectorPartitionFunction_pos Ω mu hweight hraise hΩ p hp).le)
    (wordBoltzmann_pos p hp _).le

theorem sectorToFockTotal_gibbs_error (hΩ : ‖Ω‖ = 1)
    (p t : Fin d → ℝ) (hp : ∀ a, 0 < p a) (R : ℕ) (hr : CutoffReady Ω mu R) :
    ‖(sectorToFockTotal Ω mu R).toLinearMap (sectorGibbsDensity Ω mu hweight hraise p) -
      rootThermalState t‖ ≤ gibbsThermalCutoffError Ω mu hweight hraise p t R := by
  let M : Matrix (CutoffIndex d R) (CutoffIndex d R) ℂ :=
    Matrix.diagonal (fun i => (sectorOccupationWeight Ω mu hweight hraise p (cutoffOccupation d R i).val : ℂ))
  have hfirst : ‖(sectorToFockTotal Ω mu R).toLinearMap (sectorGibbsDensity Ω mu hweight hraise p) -
      frameMatrix (cutoffNumberFrame d R) M‖ ≤
      ‖sectorGibbsDensity Ω mu hweight hraise p - sectorGibbsCutoff Ω mu hweight hraise p R‖ := by
    rw [sectorToFockTotal_eq Ω mu R hr, ← sectorToFock_matrix Ω mu R hr.1 hr.2 M]
    exact (sectorToFock Ω mu R hr.1 hr.2).toPositiveTracePreservingMap.norm_map_sub_le _ _
      (sectorGibbsDensity_nonneg Ω mu hweight hraise hΩ p hp)
      (frameMatrix_diagonal_nonneg _ _ (fun i => sectorOccupationWeight_nonneg Ω mu hweight hraise hΩ p hp _))
  have hsecond : ‖frameMatrix (cutoffNumberFrame d R) M - rootThermalCutoff t R‖ ≤
      gibbsThermalCoefficientError Ω mu hweight hraise p t R :=
    frameMatrix_diagonal_sub_norm_le _ (cutoffNumberFrame_orthonormal d R).norm_eq_one _ _
  calc
    _ ≤ ‖(sectorToFockTotal Ω mu R).toLinearMap (sectorGibbsDensity Ω mu hweight hraise p) -
        frameMatrix (cutoffNumberFrame d R) M‖ +
        ‖frameMatrix (cutoffNumberFrame d R) M - rootThermalState t‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ _ := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (frameMatrix (cutoffNumberFrame d R) M)
        (rootThermalCutoff t R) (rootThermalState t)
      rw [norm_sub_rev (rootThermalCutoff t R)] at ht
      unfold gibbsThermalCutoffError
      linarith

theorem fockToSectorTotal_gibbs_error (hΩ : ‖Ω‖ = 1)
    (p t : Fin d → ℝ) (hp : ∀ a, 0 < p a) (ht : ∀ a, 0 < t a) (htord : StrictAnti t)
    (R : ℕ) (hr : CutoffReady Ω mu R) :
    ‖(fockToSectorTotal Ω mu R hΩ).toLinearMap (rootThermalState t) -
      sectorGibbsDensity Ω mu hweight hraise p‖ ≤ gibbsThermalCutoffError Ω mu hweight hraise p t R := by
  let M : Matrix (CutoffIndex d R) (CutoffIndex d R) ℂ :=
    Matrix.diagonal (fun i => (bosonicOccupationWeight t (cutoffOccupation d R i).val : ℂ))
  have hfirst : ‖(fockToSectorTotal Ω mu R hΩ).toLinearMap (rootThermalState t) -
      frameMatrix (cutoffSectorFrame Ω mu R) M‖ ≤ ‖rootThermalState t - rootThermalCutoff t R‖ := by
    rw [fockToSectorTotal_eq Ω mu R hΩ hr, ← fockToSector_matrix Ω mu R hΩ hr.1 hr.2 M]
    exact (fockToSector Ω mu R hΩ hr.1 hr.2).toPositiveTracePreservingMap.norm_map_sub_le _ _
      (rootThermalState_nonneg t ht htord)
      (frameMatrix_diagonal_nonneg _ _ (fun i => bosonicOccupationWeight_nonneg t ht htord _))
  have hsecond : ‖frameMatrix (cutoffSectorFrame Ω mu R) M - sectorGibbsCutoff Ω mu hweight hraise p R‖ ≤
      gibbsThermalCoefficientError Ω mu hweight hraise p t R := by
    rw [norm_sub_rev]
    exact frameMatrix_diagonal_sub_norm_le _ (cutoffSectorFrame_orthonormal Ω mu R hr.2).norm_eq_one _ _
  calc
    _ ≤ ‖(fockToSectorTotal Ω mu R hΩ).toLinearMap (rootThermalState t) -
        frameMatrix (cutoffSectorFrame Ω mu R) M‖ +
        ‖frameMatrix (cutoffSectorFrame Ω mu R) M - sectorGibbsDensity Ω mu hweight hraise p‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ _ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub (frameMatrix (cutoffSectorFrame Ω mu R) M)
        (sectorGibbsCutoff Ω mu hweight hraise p R) (sectorGibbsDensity Ω mu hweight hraise p)
      rw [norm_sub_rev (sectorGibbsCutoff Ω mu hweight hraise p R)] at htri
      unfold gibbsThermalCutoffError
      linarith

end Cloning.TensorLie
