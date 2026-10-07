import Cloning.TensorCartanFrame
import Cloning.TensorCyclicSector
import Mathlib.Data.Finset.Max

/-!+# Literal last-slot slices for fundamental tensor branching

These maps act on the actual physical tensor register. The generator formula
contains the first-factor action and the single final-slot matrix unit.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Contraction of the last tensor slot against its actual computational basis. -/
def lastSlice (r : Fin d) : TensorRegister (n + 1) (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  LinearMap.toContinuousLinearMap {
    toFun x := ⟨fun w => x (Fin.snoc w r), memℓp_gen (by
      simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩
    map_add' _ _ := by ext; rfl
    map_smul' _ _ := by ext; rfl }

@[simp] theorem lastSlice_apply (r : Fin d) (x : TensorRegister (n + 1) (Fin d))
    (w : Fin n → Fin d) : lastSlice r x w = x (Fin.snoc w r) := rfl

theorem lastSlice_ext {x y : TensorRegister (n + 1) (Fin d)}
    (h : ∀ r : Fin d, lastSlice r x = lastSlice r y) : x = y := by
  ext w
  have he := congrArg (fun z : TensorRegister n (Fin d) => z (Fin.init w)) (h (w (Fin.last n)))
  simpa only [lastSlice_apply, Fin.snoc_init_self] using he

theorem lastSlice_tensorJoin (r : Fin d) (x : TensorRegister n (Fin d))
    (y : TensorRegister 1 (Fin d)) :
    lastSlice r (tensorJoin x y) = y (fun _ => r) • x := by
  ext w
  have hl : (fun i : Fin n => (Fin.snoc w r : Fin (n + 1) → Fin d) (Fin.castAdd 1 i)) = w := by
    funext i
    exact Fin.snoc_castSucc (α := fun _ => Fin d) r w i
  have hr : (fun i : Fin 1 => (Fin.snoc w r : Fin (n + 1) → Fin d) (Fin.natAdd n i)) = (fun _ => r) := by
    funext i
    fin_cases i
    exact Fin.snoc_last (α := fun _ => Fin d) r w
  simp only [lastSlice_apply, tensorJoin_apply, hl, hr, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Every slice of the literal product subspace lies in its first factor. -/
theorem lastSlice_mem_tensorProductSector (P : Submodule ℂ (TensorRegister n (Fin d)))
    (Q : Submodule ℂ (TensorRegister 1 (Fin d)))
    {x : TensorRegister (n + 1) (Fin d)} (hx : x ∈ tensorProductSector P Q) (r : Fin d) :
    lastSlice r x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, hu, v, _, rfl⟩ := hx
      rw [lastSlice_tensorJoin]
      exact P.smul_mem _ hu
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using P.add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using P.smul_mem c ih

/-- The exact physical matrix-unit action after last-slot contraction. -/
theorem lastSlice_generator (r a b : Fin d) (x : TensorRegister (n + 1) (Fin d)) :
    lastSlice r (collectiveGenerator (n + 1) a b x) =
      collectiveGenerator n a b (lastSlice r x) + if r = a then lastSlice b x else 0 := by
  ext w
  simp only [lastSlice_apply, collectiveGenerator_apply, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, ← Fin.snoc_update, Fin.update_snoc_last,
    lp.coeFn_add, Pi.add_apply]
  split_ifs <;> rfl

/-- A nonzero tensor has a largest nonzero last-slot slice. -/
theorem exists_maximal_lastSlice (x : TensorRegister (n + 1) (Fin d)) (hx : x ≠ 0) :
    ∃ r : Fin d, lastSlice r x ≠ 0 ∧ ∀ s, r < s → lastSlice s x = 0 := by
  classical
  let S : Finset (Fin d) := Finset.univ.filter (fun r => lastSlice r x ≠ 0)
  have hS : S.Nonempty := by
    by_contra hn
    apply hx
    apply lastSlice_ext
    intro r
    have hr : ¬ lastSlice r x ≠ 0 := by
      intro hr
      exact hn ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
    simpa only [map_zero] using not_not.mp hr
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image S id hS
  refine ⟨r, (Finset.mem_filter.mp hr).2, ?_⟩
  intro s hrs
  by_contra hs
  have hle := hmax s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)
  exact (not_lt_of_ge hle) hrs

/-- The last nonzero slice of a highest tensor is in the first factor's
highest line; this follows from the exact slice generator formula. -/
theorem maximal_lastSlice_highest
    (Ω : TensorRegister n (Fin d)) (hΩnorm : ‖Ω‖ = 1)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (x : TensorRegister (n + 1) (Fin d))
    (hx : x ∈ tensorProductSector (cyclicSector Ω) (⊤ : Submodule ℂ (TensorRegister 1 (Fin d))))
    (hxraise : ∀ a b, a < b → collectiveGenerator (n + 1) a b x = 0)
    (r : Fin d) (htail : ∀ s, r < s → lastSlice s x = 0) :
    lastSlice r x = ⟪Ω, lastSlice r x⟫_ℂ • Ω := by
  apply cyclicSector_raising_kernel Ω hΩnorm hΩraise
    (lastSlice_mem_tensorProductSector _ _ hx r)
  intro a b hab
  have h := congrArg (lastSlice r) (hxraise a b hab)
  rw [lastSlice_generator, map_zero] at h
  by_cases hra : r = a
  · subst a
    simpa [htail b hab] using h
  · simpa only [if_neg hra, add_zero] using h

end Cloning.TensorLie
