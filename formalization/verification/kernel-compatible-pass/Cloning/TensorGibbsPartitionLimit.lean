import Cloning.TensorGibbsBosonicPartition
import Mathlib.Analysis.Normed.Group.Tannery

/-! The physical sector character normalization follows from PBW independence
at fixed height and a derived summable height envelope. Moving spectra are
allowed; no character formula or partition limit is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def partitionHeightMass (mu : Fin d → ℕ) (hmu : Antitone mu) (p : Fin d → ℝ) (H : ℕ) : ℝ :=
  sectorHeightMass (partitionHighestTensor mu hmu) mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p H

theorem partition_eventually_heightMass_eq_bosonic
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2)
    (pN : ℕ → Fin d → ℝ) (hpN : ∀ᶠ N in atTop, ∀ a, 0 < pN N a) (H : ℕ) :
    ∀ᶠ N in atTop, partitionHeightMass (mu N) (hmu N) (pN N) H = bosonicHeightMass (pN N) H := by
  classical
  have hwords : ∀ k l : HeightOccupation d H,
      (canonicalWord k.val).Perm (canonicalWord l.val) ↔ k = l := by
    intro k l
    rw [canonicalWord_perm_iff, Subtype.val_inj]
  have hli := partition_normalizedWord_eventually_linearIndependent
    (fun a : PositiveRoot d => a) Function.injective_id mu hmu δ hδ hgap
    (fun k : HeightOccupation d H => canonicalWord k.val) hwords
  have hpos : ∀ᶠ N in atTop, 0 < δ N := hδ.eventually (eventually_gt_atTop 0)
  filter_upwards [hli, hgap, hpos, hpN] with N hN hg hd hp
  exact sectorHeightMass_eq_bosonic _ _ _ _ (pN N) hp H
    (fun a => hd.trans_le (hg a)) hN

theorem bosonicHeightMass_tendsto (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a))) (H : ℕ) :
    Tendsto (fun N => bosonicHeightMass (pN N) H) atTop (𝓝 (bosonicHeightMass p H)) := by
  simp only [bosonicHeightMass, wordBoltzmann_canonicalWord]
  apply tendsto_finset_sum
  intro k _
  apply tendsto_finset_prod
  intro r _
  exact (rootBoltzmann_tendsto pN p hp hlim r).pow _

/-- Actual sector trace divided by its actual highest eigenvalue converges to
its product geometric partition function, even for moving spectra. -/
theorem sectorPartitionFunction_div_highest_tendsto
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2)
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a))) :
    Tendsto (fun N =>
      sectorPartitionFunction (partitionHighestTensor (mu N) (hmu N)) (mu N)
        (partitionHighestTensor_cartan (mu N) (hmu N))
        (partitionHighestTensor_raising_zero (mu N) (hmu N)) (pN N) /
          (∏ a, pN N a ^ mu N a)) atTop
      (𝓝 (∏ r : PositiveRoot d, (1-rootBoltzmann p r)⁻¹)) := by
  have hpN : ∀ᶠ N in atTop, ∀ a, 0 < pN N a :=
    Filter.eventually_all.mpr (fun a => (hlim a).eventually (eventually_gt_nhds (hp a)))
  obtain ⟨θ, hθ, hθ1, _, hroot⟩ := exists_eventual_root_height_decay pN p hp hord hlim
  have hpoint (H : ℕ) : Tendsto (fun N => partitionHeightMass (mu N) (hmu N) (pN N) H)
      atTop (𝓝 (bosonicHeightMass p H)) :=
    (bosonicHeightMass_tendsto pN p hp hlim H).congr'
      (by
        filter_upwards [partition_eventually_heightMass_eq_bosonic mu hmu δ hδ hgap pN hpN H] with N hN
        exact hN.symm)
  have hbound : ∀ᶠ N in atTop, ∀ H,
      ‖partitionHeightMass (mu N) (hmu N) (pN N) H‖ ≤ heightEnvelope d θ H := by
    filter_upwards [hpN, hroot] with N hN hr H
    dsimp only [partitionHeightMass]
    rw [Real.norm_eq_abs, abs_of_nonneg (sectorHeightMass_nonneg _ _ _ _ _ hN H)]
    exact sectorHeightMass_le_envelope _ _ _ _ _ hN θ hθ.le hr H
  have ht := tendsto_tsum_of_dominated_convergence (heightEnvelope_summable (d := d) θ hθ hθ1)
    hpoint hbound
  rw [(bosonicHeightMass_hasSum p hp hord).tsum_eq] at ht
  apply ht.congr'
  filter_upwards [hpN] with N hN
  exact (sectorPartitionFunction_div_highest _ _ _ _ _ hN).symm

end Cloning.TensorLie
