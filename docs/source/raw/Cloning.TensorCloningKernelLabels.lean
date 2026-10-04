import Cloning.TensorCloningKernel

/-! Exact recovery of the randomized physical Young-label kernel from the
copy-level global cloning channel. -/
noncomputable section
open scoped BigOperators Classical ENNReal
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem integerCopyLabel_isYoung (n d : ℕ) (i : SchurCopy n (d+1)) :
    IsYoung (n : ℤ) (integerCopyLabel n d i) := by
  let H := (recursivePhysicalDecomposition n (d+1)).get i
  refine ⟨fun a ↦ Int.natCast_nonneg _, ?_, ?_⟩
  · intro a b hab
    change (H.weight b : ℤ) ≤ (H.weight a : ℤ)
    exact_mod_cast H.weight_antitone hab
  · change (∑ a, (H.weight a : ℤ)) = (n : ℤ)
    exact_mod_cast H.weight_sum

/-- No valid output partition triggers the extra copy-selection fallback. -/
theorem exists_copy_integer_label (n d : ℕ) (ν : Fin (d+1) → ℤ)
    (hν : IsYoung (n : ℤ) ν) : ∃ j : SchurCopy n (d+1), integerCopyLabel n d j = ν := by
  let μ : Fin (d+1) → ℕ := fun i ↦ (ν i).toNat
  have hm : Antitone μ := fun i j hij ↦ Int.toNat_le_toNat (hν.2.1 hij)
  have hs : ∑ i, μ i = n := by
    apply Int.ofNat_inj.mp
    push_cast
    simpa only [μ, Int.toNat_of_nonneg (hν.1 _)] using hν.2.2
  obtain ⟨j, hj⟩ := exists_copy_weight μ hm hs
  refine ⟨j, ?_⟩
  funext i
  simp only [integerCopyLabel, hj, μ, Int.toNat_of_nonneg (hν.1 i)]

theorem universalCopyPMF_label (n m d : ℕ) (i : SchurCopy n (d+1)) :
    (universalCopyPMF n m d i).map (integerCopyLabel m d) =
      fallbackKernel ((m : ℝ)/(n : ℝ)) (n : ℤ) (m : ℤ) (integerCopyLabel n d i) := by
  let P := fallbackKernel ((m : ℝ)/(n : ℝ)) (n : ℤ) (m : ℤ) (integerCopyLabel n d i)
  change (P.bind (uniformFiberPMF (integerCopyLabel m d) (fallbackCopy m d))).map
    (integerCopyLabel m d) = P
  rw [PMF.map_bind]
  have he : P.bind (fun a ↦ (uniformFiberPMF (integerCopyLabel m d) (fallbackCopy m d) a).map
      (integerCopyLabel m d)) = P.bind PMF.pure := by
    apply PMF.ext
    intro a
    rw [PMF.bind_apply, PMF.bind_apply]
    apply tsum_congr
    intro ν
    by_cases hν : P ν = 0
    · simp [hν]
    · have hv := fallbackKernel_support_isYoung ((m : ℝ)/(n : ℝ)) n m
        (by omega) (integerCopyLabel n d i) (integerCopyLabel_isYoung n d i) ν hν
      rw [uniformFiberPMF_label _ _ ν (exists_copy_integer_label m d ν hv)]
  rw [he, PMF.bind_pure]

end Cloning.TensorCloning
