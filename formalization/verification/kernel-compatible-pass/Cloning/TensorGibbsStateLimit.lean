import Cloning.TensorGibbsStateTransfer

/-! Moving-spectrum centered sector LAN follows from the derived partition
normalization and actual finite-frame channel action. -/
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
variable (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2)
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))

include δ hδ hgap hp hord hlim

theorem sectorOccupationWeight_tendsto (k : PositiveRoot d → ℕ) :
    Tendsto (fun N => sectorOccupationWeight (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) k)
      atTop (𝓝 (bosonicOccupationWeight p k)) := by
  have hz := sectorPartitionFunction_div_highest_tendsto mu hmu δ hδ hgap pN p hp hord hlim
  have hc : (∏ r : PositiveRoot d, (1-rootBoltzmann p r)⁻¹) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ => inv_ne_zero (sub_pos.mpr (rootBoltzmann_lt_one p hp hord r)).ne')
  have hi := hz.inv₀ hc
  simp only [inv_div, Finset.prod_inv_distrib, inv_inv] at hi
  have hw : Tendsto (fun N => wordBoltzmann (pN N) (canonicalWord k)) atTop
      (𝓝 (wordBoltzmann p (canonicalWord k))) := by
    simp only [wordBoltzmann_canonicalWord]
    exact tendsto_finset_prod _ (fun r _ => (rootBoltzmann_tendsto pN p hp hlim r).pow (k r))
  exact hi.mul hw

theorem gibbsThermalCoefficientError_tendsto_zero (R : ℕ) :
    Tendsto (fun N => gibbsThermalCoefficientError (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) p R) atTop (𝓝 0) := by
  have ht := tendsto_finset_sum (Finset.univ : Finset (CutoffIndex d R)) (fun i _ =>
    ((sectorOccupationWeight_tendsto mu hmu δ hδ hgap pN p hp hord hlim
      (cutoffOccupation d R i).val).sub (tendsto_const_nhds
        (x := bosonicOccupationWeight p (cutoffOccupation d R i).val))).abs)
  simpa only [sub_self, abs_zero, Finset.sum_const_zero] using ht

theorem sectorGibbsCutoff_error_tendsto_thermalTail (R : ℕ) :
    Tendsto (fun N => ‖sectorGibbsDensity (partitionHighestTensor (mu N) (hmu N)) (mu N)
        (partitionHighestTensor_cartan (mu N) (hmu N))
        (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) -
      sectorGibbsCutoff (partitionHighestTensor (mu N) (hmu N)) (mu N)
        (partitionHighestTensor_cartan (mu N) (hmu N))
        (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) R‖) atTop
      (𝓝 ‖rootThermalState p - rootThermalCutoff p R‖) := by
  have hpN : ∀ᶠ N in atTop, ∀ a, 0 < pN N a :=
    Filter.eventually_all.mpr (fun a => (hlim a).eventually (eventually_gt_nhds (hp a)))
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_finset_sum (Finset.univ : Finset (CutoffIndex d R))
    (fun i _ => sectorOccupationWeight_tendsto mu hmu δ hδ hgap pN p hp hord hlim
      (cutoffOccupation d R i).val))
  have he : (1 : ℝ) - ∑ i : CutoffIndex d R, bosonicOccupationWeight p (cutoffOccupation d R i).val =
      ‖rootThermalState p - rootThermalCutoff p R‖ := by
    rw [rootThermalCutoff_error p hp hord]
    congr 1
    exact (cutoffOccupation d R).sum_comp (fun k => bosonicOccupationWeight p k.val)
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hpN, partition_eventually_CutoffReady mu hmu δ hδ hgap R] with N hN hr
  exact (sectorGibbsCutoff_error _ _ _ _ (partitionHighestTensor_norm _ _) _ hN R hr.2).symm

theorem gibbsThermalCutoffError_tendsto (R : ℕ) :
    Tendsto (fun N => gibbsThermalCutoffError (partitionHighestTensor (mu N) (hmu N)) (mu N)
      (partitionHighestTensor_cartan (mu N) (hmu N))
      (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) p R) atTop
      (𝓝 (2 * ‖rootThermalState p - rootThermalCutoff p R‖)) := by
  have ht := ((sectorGibbsCutoff_error_tendsto_thermalTail mu hmu δ hδ hgap pN p hp hord hlim R).add
    (gibbsThermalCoefficientError_tendsto_zero mu hmu δ hδ hgap pN p hp hord hlim R)).add
      (tendsto_const_nhds (x := ‖rootThermalState p - rootThermalCutoff p R‖))
  simpa only [gibbsThermalCutoffError, add_zero, two_mul] using ht

/-- Given any accuracy, a fixed genuine cutoff works eventually in both
channel directions; it can be required to exceed any prescribed cutoff. -/
theorem exists_cutoff_eventually_twoWay_gibbs (ε : ℝ) (hε : 0 < ε) (Rmin : ℕ) :
    ∃ R ≥ Rmin, ∀ᶠ N in atTop,
      ‖(sectorToFockTotal (partitionHighestTensor (mu N) (hmu N)) (mu N) R).toLinearMap
        (sectorGibbsDensity (partitionHighestTensor (mu N) (hmu N)) (mu N)
          (partitionHighestTensor_cartan (mu N) (hmu N))
          (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N)) - rootThermalState p‖ < ε ∧
      ‖(fockToSectorTotal (partitionHighestTensor (mu N) (hmu N)) (mu N) R
          (partitionHighestTensor_norm _ _)).toLinearMap (rootThermalState p) -
        sectorGibbsDensity (partitionHighestTensor (mu N) (hmu N)) (mu N)
          (partitionHighestTensor_cartan (mu N) (hmu N))
          (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N)‖ < ε := by
  have ht := (rootThermalCutoff_error_tendsto_zero p hp hord).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε/2 by positivity))
  obtain ⟨R, hR, hsmall⟩ := ((eventually_ge_atTop Rmin).and ht).exists
  refine ⟨R,hR,?_⟩
  have hb := (gibbsThermalCutoffError_tendsto mu hmu δ hδ hgap pN p hp hord hlim R).eventually
    (eventually_lt_nhds (show 2 * ‖rootThermalState p - rootThermalCutoff p R‖ < ε by linarith))
  have hpN : ∀ᶠ N in atTop, ∀ a, 0 < pN N a :=
    Filter.eventually_all.mpr (fun a => (hlim a).eventually (eventually_gt_nhds (hp a)))
  filter_upwards [hb, hpN, partition_eventually_CutoffReady mu hmu δ hδ hgap R] with N hN hn hr
  exact ⟨(sectorToFockTotal_gibbs_error _ _ _ _ (partitionHighestTensor_norm _ _) _ _ hn R hr).trans_lt hN,
    (fockToSectorTotal_gibbs_error _ _ _ _ (partitionHighestTensor_norm _ _) _ _ hn hp hord R hr).trans_lt hN⟩

end Cloning.TensorLie
