import Cloning.TensorCloningUniversalSupport

/-! Retained randomized output copies have the correct physical row
frequencies along arbitrary compact-spectrum subsequences. -/
noncomputable section
open scoped BigOperators Classical Topology
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem rounded_scaled_tendsto {d : ℕ} (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (mu nu : ℕ → Fin d → ℕ) (p : Fin d → ℝ) (γ C : ℝ)
    (hgain : Tendsto (fun k ↦ (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (hmu : ∀ a, Tendsto (fun k ↦ (mu k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a)))
    (herr : ∀ᶠ k in atTop, ∀ a,
      |(nu k a : ℝ) - ((m k : ℝ)/(n k : ℝ))*(mu k a : ℝ)| ≤
        C*((((m k : ℝ)/(n k : ℝ))+1)/2)) (a : Fin d) :
    Tendsto (fun k ↦ (nu k a : ℝ)/(n k : ℝ)) atTop (𝓝 (γ*p a)) := by
  have hb : Tendsto (fun k ↦ (C*((((m k : ℝ)/(n k : ℝ))+1)/2))/(n k : ℝ))
      atTop (𝓝 0) := ((hgain.add_const 1).div_const 2).const_mul C |>.div_atTop
        (tendsto_natCast_atTop_atTop.comp hn)
  have he : Tendsto (fun k ↦ (nu k a : ℝ)/(n k : ℝ) -
      ((m k : ℝ)/(n k : ℝ))*((mu k a : ℝ)/(n k : ℝ))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _) ?_ hb
    filter_upwards [herr, hn.eventually (eventually_gt_atTop 0)] with k hk hn0
    have hnr : (0 : ℝ) < n k := by exact_mod_cast hn0
    rw [Real.norm_eq_abs, show (nu k a : ℝ)/(n k : ℝ) -
      ((m k : ℝ)/(n k : ℝ))*((mu k a : ℝ)/(n k : ℝ)) =
      ((nu k a : ℝ) - ((m k : ℝ)/(n k : ℝ))*(mu k a : ℝ))/(n k : ℝ) by ring,
      abs_div, abs_of_pos hnr]
    exact div_le_div_of_nonneg_right (hk a) hnr.le
  have h := he.add (hgain.mul (hmu a))
  simpa only [sub_add_cancel, zero_add] using h

theorem universalKeep_scaled_limits {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d+1) → ℝ)) (hK : IsCompact K)
    (hp : ∀ p ∈ K, ∀ a, 0 < p a) (hord : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (pN : ℕ → Fin (d+1) → ℝ) (hpK : ∀ k, pN k ∈ K)
    (p : Fin (d+1) → ℝ) (hplim : ∀ a, Tendsto (fun k ↦ pN k a) atTop (𝓝 (p a)))
    (i : (k : ℕ) → SchurCopy (n k) (d+1))
    (j : (k : ℕ) → SchurCopy (m (n k)) (d+1))
    (hkeep : ∀ k, universalKeep (n k) (m (n k)) d (pN k) (i k) (j k)) :
    (∀ a, Tendsto (fun k ↦ (((recursivePhysicalDecomposition (n k) (d+1)).get (i k)).weight a : ℝ)/(n k : ℝ))
      atTop (𝓝 (p a))) ∧
    (∀ a, Tendsto (fun k ↦ (((recursivePhysicalDecomposition (m (n k)) (d+1)).get (j k)).weight a : ℝ)/(n k : ℝ))
      atTop (𝓝 (γ*p a))) := by
  let mu : ℕ → Fin (d+1) → ℕ := fun k ↦ ((recursivePhysicalDecomposition (n k) (d+1)).get (i k)).weight
  let nu : ℕ → Fin (d+1) → ℕ := fun k ↦ ((recursivePhysicalDecomposition (m (n k)) (d+1)).get (j k)).weight
  have hm : ∀ a, Tendsto (fun k ↦ (mu k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a)) :=
    typicalLabel_ratio_tendsto n hn mu pN p hplim (Eventually.of_forall (fun k ↦ (hkeep k).1))
  refine ⟨hm, ?_⟩
  have hs := hn.eventually (eventually_universalKeep_support hd K hK hp hord m γ hγ hgain)
  apply rounded_scaled_tendsto n (fun k ↦ m (n k)) hn mu nu p γ (d : ℝ) (hgain.comp hn) hm
  filter_upwards [hs] with k hk a
  have hh := (hk (pN k) (hpK k) (i k) (j k) (hkeep k)).2 a
  simpa only [integerCopyLabel, Int.cast_natCast, mu, nu] using hh

end Cloning.TensorCloning
