import Cloning.TensorCloningUniversalProbability
import Cloning.TensorCloningAchievabilityCompatibility

/-! Actual retained universal transitions have the deterministic rounding
error and admissible Cartan difference, uniformly on compact spectra. -/
noncomputable section
open scoped BigOperators Classical Topology
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem partitionCompatible_of_integer (n m d : ℕ)
    (i : SchurCopy n (d+1)) (j : SchurCopy m (d+1))
    (h : Compatible n m (integerCopyLabel n d i) (integerCopyLabel m d j)) :
    PartitionCompatible ((recursivePhysicalDecomposition n (d+1)).get i).weight
      ((recursivePhysicalDecomposition m (d+1)).get j).weight := by
  have hle (a : Fin (d+1)) : ((recursivePhysicalDecomposition n (d+1)).get i).weight a ≤
      ((recursivePhysicalDecomposition m (d+1)).get j).weight a := by
    have ha := sub_nonneg.mp (h.1 a)
    unfold integerCopyLabel at ha
    exact_mod_cast ha
  refine ⟨hle, ?_⟩
  intro a b hab
  have hh := h.2.1 hab
  unfold integerCopyLabel at hh
  have hh' : (((((recursivePhysicalDecomposition m (d+1)).get j).weight b -
      ((recursivePhysicalDecomposition n (d+1)).get i).weight b : ℕ)) : ℤ) ≤
      (((((recursivePhysicalDecomposition m (d+1)).get j).weight a -
      ((recursivePhysicalDecomposition n (d+1)).get i).weight a : ℕ)) : ℤ) := by
    simpa only [Nat.cast_sub (hle _)] using hh
  exact_mod_cast hh'

theorem eventually_universalKeep_support {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d+1) → ℝ)) (hK : IsCompact K)
    (hp : ∀ p ∈ K, ∀ a, 0 < p a) (hord : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun n ↦ (m n : ℝ)/n) atTop (𝓝 γ)) :
    ∀ᶠ n in atTop, ∀ p ∈ K, ∀ (i : SchurCopy n (d+1)) (j : SchurCopy (m n) (d+1)),
      universalKeep n (m n) d p i j →
      PartitionCompatible ((recursivePhysicalDecomposition n (d+1)).get i).weight
        ((recursivePhysicalDecomposition (m n) (d+1)).get j).weight ∧
      ∀ a, |(integerCopyLabel (m n) d j a : ℝ) -
        ((m n : ℝ)/n) * (integerCopyLabel n d i a : ℝ)| ≤
          (d : ℝ)*((((m n : ℝ)/n)+1)/2) := by
  let mz : ℕ → ℤ := fun n ↦ if n = 0 then 0 else m n
  have hmz n : (mz n : ℝ) = ((m n : ℝ)/n)*(n : ℝ) := by
    by_cases hn : n = 0
    · simp [mz, hn]
    · simp [mz, hn, div_mul_cancel₀ _ (by exact_mod_cast hn : (n : ℝ) ≠ 0)]
  obtain ⟨a, ha, hpos, hgap⟩ := compact_spectra_positive_gap K hK hp hord
  have he := eventually_rounding_support_compatible hd mz (fun n ↦ (m n : ℝ)/n)
    shrinkingRadius γ a ha hγ hgain shrinkingRadius_tendsto_zero hmz
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn0
  intro p hpK i j hij
  have hm : mz n = (m n : ℤ) := by simp [mz, show n ≠ 0 by omega]
  have hrow (z : Fin d → ℤ)
      (hz : YoungRounding.roundingPMF ((m n : ℝ)/n)
        (fun a ↦ (integerCopyLabel n d i a.castSucc : ℝ)) z ≠ 0) :
      Compatible n (m n) (integerCopyLabel n d i) (complete (m n) z) := by
    have hh := hn p (hpos p hpK) (hgap p hpK) (integerCopyLabel n d i)
      (integerCopyLabel_isYoung n d i).2.2
      (fun a ↦ (show |(((recursivePhysicalDecomposition n (d+1)).get i).weight a : ℝ)-n*p a| <
        n*shrinkingRadius n from hij.1 a).le) z hz
    simpa only [hm] using hh
  have hsupport := universalKeep_label_support n (m n) d p i j hij
  rw [fallbackKernel_eq_raw_of_support _ _ _ _ hrow] at hsupport
  obtain ⟨z, hz, hj⟩ := (PMF.mem_support_map_iff _ _ _).mp hsupport
  have hc := hrow z hz
  rw [hj] at hc
  refine ⟨partitionCompatible_of_integer n (m n) d i j hc, ?_⟩
  intro b
  have hb := complete_rounding_support_error hd n (m n) (integerCopyLabel n d i)
    ((m n : ℝ)/n) (by positivity) (integerCopyLabel_isYoung n d i).2.2
    (by simpa only [hm] using hmz n) z hz b
  rw [hj] at hb
  simpa only [integerCopyLabel, Int.cast_natCast] using hb

end Cloning.TensorCloning
