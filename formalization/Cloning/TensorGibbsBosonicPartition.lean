import Cloning.TensorGibbsHeightSpectrum
import Cloning.Thermal

/-! The sum of the finite height occupation laws is the genuine product
geometric partition function. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem wordBoltzmann_canonicalWord (p : Fin d → ℝ) (k : PositiveRoot d → ℕ) :
    wordBoltzmann p (canonicalWord k) = ∏ r, rootBoltzmann p r ^ k r := by
  unfold wordBoltzmann
  rw [Finset.prod_list_map_count]
  have hs : (∏ r ∈ (canonicalWord k).toFinset,
      rootBoltzmann p r ^ (canonicalWord k).count r) =
      ∏ r : PositiveRoot d, rootBoltzmann p r ^ (canonicalWord k).count r := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro r _ hr
    simp only [List.mem_toFinset] at hr
    rw [List.count_eq_zero.mpr hr, pow_zero]
  calc
    _ = ∏ r : PositiveRoot d, rootBoltzmann p r ^ (canonicalWord k).count r := by
      simpa only [List.count, beq_eq_decide] using hs
    _ = _ := by simp only [canonicalWord_count]

def occupationHeightEquiv : (Σ H : ℕ, ExactHeightOccupation d H) ≃ (PositiveRoot d → ℕ) where
  toFun k := k.2.val.val
  invFun k := ⟨occupationHeight k, ⟨⟨k,le_rfl⟩,rfl⟩⟩
  left_inv := by rintro ⟨H,⟨⟨k,hk⟩,he⟩⟩; dsimp at he; subst H; rfl
  right_inv := by intro k; rfl

theorem rootPowerProduct_hasSum (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) :
    HasSum (fun k : PositiveRoot d → ℕ => ∏ r, rootBoltzmann p r ^ k r)
      (∏ r : PositiveRoot d, (1-rootBoltzmann p r)⁻¹) := by
  classical
  let e : Fin (Fintype.card (PositiveRoot d)) ≃ PositiveRoot d := (Fintype.equivFin _).symm
  let E := Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← E.hasSum_iff]
  have hs := Thermal.hasSum_fin_product (Fintype.card (PositiveRoot d))
    (fun i k => rootBoltzmann p (e i) ^ k)
    (fun i => (1-rootBoltzmann p (e i))⁻¹)
    (fun i k => pow_nonneg (div_pos (hp _) (hp _)).le k)
    (fun i => hasSum_geometric_of_lt_one (div_pos (hp _) (hp _)).le
      (rootBoltzmann_lt_one p hp hord (e i)))
  convert hs using 1
  · funext k
    change (∏ r, rootBoltzmann p r ^ k (e.symm r)) = _
    simpa only [e.symm_apply_apply] using (e.prod_comp (fun r => rootBoltzmann p r ^ k (e.symm r))).symm
  · exact (e.prod_comp (fun r => (1-rootBoltzmann p r)⁻¹)).symm

theorem bosonicHeightMass_hasSum (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) :
    HasSum (bosonicHeightMass p) (∏ r : PositiveRoot d, (1-rootBoltzmann p r)⁻¹) := by
  have hs := (occupationHeightEquiv (d := d)).hasSum_iff.mpr (rootPowerProduct_hasSum p hp hord)
  have he := hs.summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)
  have hs' := hs.summable.sigma
  have hf : (fun H : ℕ => ∑' k : ExactHeightOccupation d H,
      ∏ r, rootBoltzmann p r ^ k.val.val r) = bosonicHeightMass p := by
    funext H
    simp only [tsum_fintype, bosonicHeightMass, wordBoltzmann_canonicalWord]
  change Summable (fun H : ℕ => ∑' k : ExactHeightOccupation d H,
      ∏ r, rootBoltzmann p r ^ k.val.val r) at hs'
  rw [hf] at hs'
  apply hs'.hasSum_iff.mpr
  rw [← hs.tsum_eq, he]
  change (∑' H, bosonicHeightMass p H) = ∑' H, ∑' k : ExactHeightOccupation d H,
    ∏ r, rootBoltzmann p r ^ k.val.val r
  rw [hf]

end Cloning.TensorLie
