import Cloning.TensorFundamentalBranchingSlices
import Cloning.YoungBranchingStandard

/-! Exact highest-weight classification for a physical cyclic sector tensored
with one particle. The proof uses its largest nonzero physical last-slot slice. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem addBox_injective (mu : Fin d → ℕ) : Function.Injective (addBox mu) := by
  intro r s h
  by_contra hrs
  have he := congrFun h r
  simp [addBox, hrs] at he

/-- The largest nonzero slice forces the exact one-box highest weight. -/
theorem maximal_lastSlice_weight
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (x : TensorRegister (n + 1) (Fin d)) (lambda : Fin d → ℕ)
    (hx : x ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))))
    (hxweight : ∀ a, collectiveGenerator (n + 1) a a x = (lambda a : ℂ) • x)
    (hxraise : ∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0)
    (r : Fin d) (hr : lastSlice r x ≠ 0) (htail : ∀ s, r < s → lastSlice s x = 0) :
    lambda = addBox mu r := by
  have hline := maximal_lastSlice_highest Ω hΩnorm hΩraise x hx hxraise r htail
  funext a
  have hw : collectiveGenerator n a a (lastSlice r x) = (mu a : ℂ) • lastSlice r x := by
    rw [hline, map_smul, hΩweight]
    exact smul_comm _ _ _
  have he := congrArg (lastSlice r) (hxweight a)
  rw [lastSlice_generator, map_smul, hw] at he
  have hscalar : ((mu a + if a = r then 1 else 0 : ℕ) : ℂ) • lastSlice r x =
      (lambda a : ℂ) • lastSlice r x := by
    by_cases har : a = r
    · subst a
      simpa [Nat.cast_add, add_smul] using he
    · simpa [har, Ne.symm har] using he
  have heq : ((mu a + if a = r then 1 else 0 : ℕ) : ℂ) = (lambda a : ℂ) :=
    smul_left_injective ℂ hr hscalar
  have hn : mu a + (if a = r then 1 else 0) = lambda a := by exact_mod_cast heq
  exact hn.symm

/-- Every nonzero physical highest tensor in `S_mu ⊗ C^d` has weight `mu+e_r`.
Both the row and its nonzero highest slice are constructed, not assumed. -/
theorem highest_onebox_classification
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (x : TensorRegister (n + 1) (Fin d)) (lambda : Fin d → ℕ)
    (hx : x ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))))
    (hxweight : ∀ a, collectiveGenerator (n + 1) a a x = (lambda a : ℂ) • x)
    (hxraise : ∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0) (hx0 : x ≠ 0) :
    ∃ r : Fin d, lambda = addBox mu r ∧ lastSlice r x ≠ 0 ∧
      ∀ s, r < s → lastSlice s x = 0 := by
  obtain ⟨r, hr, htail⟩ := exists_maximal_lastSlice x hx0
  exact ⟨r, maximal_lastSlice_weight Ω mu hΩnorm hΩweight hΩraise x lambda
    hx hxweight hxraise r hr htail, hr, htail⟩

theorem highest_onebox_lastSlice_vanish_above
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (x : TensorRegister (n + 1) (Fin d)) (r : Fin d)
    (hx : x ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))))
    (hxweight : ∀ a, collectiveGenerator (n + 1) a a x = (addBox mu r a : ℂ) • x)
    (hxraise : ∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0) :
    ∀ s, r < s → lastSlice s x = 0 := by
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  · obtain ⟨r', he, _, ht⟩ := highest_onebox_classification Ω mu hΩnorm hΩweight hΩraise
      x (addBox mu r) hx hxweight hxraise hx0
    have hr : r = r' := addBox_injective mu he
    simpa only [hr] using ht

/-- Within one candidate highest weight, the leading physical slice detects
zero. In particular there cannot be a second copy hidden in lower slices. -/
theorem highest_onebox_zero_of_lastSlice_zero
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hΩnorm : ‖Ω‖ = 1)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (x : TensorRegister (n + 1) (Fin d)) (r : Fin d)
    (hx : x ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))))
    (hxweight : ∀ a, collectiveGenerator (n + 1) a a x = (addBox mu r a : ℂ) • x)
    (hxraise : ∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0)
    (hzero : lastSlice r x = 0) : x = 0 := by
  classical
  by_contra hx0
  obtain ⟨r', he, hr, _⟩ := highest_onebox_classification Ω mu hΩnorm hΩweight hΩraise
    x (addBox mu r) hx hxweight hxraise hx0
  have hre : r = r' := addBox_injective mu he
  exact hr (hre ▸ hzero)

end Cloning.TensorLie
