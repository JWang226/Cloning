import Cloning.TensorGibbsStateLimit
import Cloning.TensorGibbsThermalIdentification
import Cloning.TensorLANEmbeddingDiagonal

/-! A single slowly diverging sequence of the actual total cutoff channels
transfers centered physical Gibbs states in both directions in trace norm. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.TensorLAN
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def partitionGibbsForwardError (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p t : Fin d → ℝ) (R : ℕ) : ℝ :=
  ‖(sectorToFockTotal (partitionHighestTensor mu hmu) mu R).toLinearMap
    (sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p) -
    rootThermalState t‖

def partitionGibbsReverseError (mu : Fin d → ℕ) (hmu : Antitone mu)
    (p t : Fin d → ℝ) (R : ℕ) : ℝ :=
  ‖(fockToSectorTotal (partitionHighestTensor mu hmu) mu R (partitionHighestTensor_norm mu hmu)).toLinearMap
    (rootThermalState t) - sectorGibbsDensity (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p‖

theorem exists_diverging_cutoff_twoWay_gibbs
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2)
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a))) :
    ∃ R : ℕ → ℕ, Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun N => partitionGibbsForwardError (mu N) (hmu N) (pN N) p (R N)) atTop (𝓝 0) ∧
      Tendsto (fun N => partitionGibbsReverseError (mu N) (hmu N) (pN N) p (R N)) atTop (𝓝 0) := by
  let bound (r : ℕ) : ℝ := 2 * ‖rootThermalState p - rootThermalCutoff p r‖ + 1 / ((r : ℝ)+1)
  let P (N r : ℕ) : Prop :=
    CutoffReady (partitionHighestTensor (mu N) (hmu N)) (mu N) r ∧ (∀ a, 0 < pN N a) ∧
    gibbsThermalCutoffError (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) p r ≤ bound r
  have hpN : ∀ᶠ N in atTop, ∀ a, 0 < pN N a :=
    Filter.eventually_all.mpr (fun a => (hlim a).eventually (eventually_gt_nhds (hp a)))
  have hP (r : ℕ) : ∀ᶠ N in atTop, P N r := by
    have hb := (gibbsThermalCutoffError_tendsto mu hmu δ hδ hgap pN p hp hord hlim r).eventually
      (eventually_lt_nhds (show 2 * ‖rootThermalState p - rootThermalCutoff p r‖ < bound r by
        dsimp [bound]; exact lt_add_of_pos_right _ (by positivity)))
    filter_upwards [partition_eventually_CutoffReady mu hmu δ hδ hgap r, hpN, hb] with N hr hn hb
    exact ⟨hr,hn,hb.le⟩
  obtain ⟨R, hmono, hR, _, he⟩ := exists_common_diverging_cutoff P hP
  have hb : Tendsto (fun N => bound (R N)) atTop (𝓝 0) := by
    have ht := ((rootThermalCutoff_error_tendsto_zero p hp hord).const_mul 2).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hc := ht.comp hR
    simpa only [mul_zero, add_zero] using hc
  refine ⟨R,hmono,hR,?_,?_⟩
  · dsimp only [partitionGibbsForwardError]
    apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_ hb
    filter_upwards [he] with N hN
    have hh := hN (R N) le_rfl
    exact (sectorToFockTotal_gibbs_error _ _ _ _ (partitionHighestTensor_norm _ _) _ _ hh.2.1 _ hh.1).trans hh.2.2
  · apply squeeze_zero' (Eventually.of_forall (fun N =>
      show 0 ≤ partitionGibbsReverseError (mu N) (hmu N) (pN N) p (R N) from norm_nonneg _)) ?_ hb
    filter_upwards [he] with N hN
    have hh := hN (R N) le_rfl
    exact (fockToSectorTotal_gibbs_error _ _ _ _ (partitionHighestTensor_norm _ _) _ _ hh.2.1 hp hord _ hh.1).trans hh.2.2

end Cloning.TensorLie
