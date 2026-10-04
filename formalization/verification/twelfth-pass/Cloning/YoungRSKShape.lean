import Cloning.YoungRSKContent

/-! Elementary shape facts for the one-box insertion bijection. -/

noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungGeneral

def shapeRemovable : List ℕ → ℕ → Prop
  | [], _ => False
  | m :: M, 0 => 0 < m ∧ ∀ n ∈ M.head?, n < m
  | _ :: M, r + 1 => shapeRemovable M r

theorem shapeAdd_injective_of_length {M K : List ℕ} (h : M.length = K.length)
    (r : ℕ) (he : shapeAdd M r = shapeAdd K r) : M = K := by
  induction M generalizing K r with
  | nil => simpa using h.symm
  | cons m M ih =>
    cases K with
    | nil => simp at h
    | cons k K =>
      have hlen : M.length = K.length := by simpa using h
      cases r with
      | zero =>
        simp only [shapeAdd, List.cons.injEq] at he
        obtain ⟨hm, hM⟩ := he
        have : m = k := by omega
        simp [this, hM]
      | succ r =>
        simp only [shapeAdd, List.cons.injEq] at he
        exact congrArg₂ List.cons he.1 (ih hlen r he.2)

theorem shapeRemovable_shapeAdd (M : List ℕ)
    (hM : List.Pairwise (fun a b => b ≤ a) M) (r : ℕ) (hr : r < M.length) :
    shapeRemovable (shapeAdd M r) r := by
  induction M generalizing r with
  | nil => simp at hr
  | cons m M ih =>
    obtain ⟨hm, hM⟩ := List.pairwise_cons.mp hM
    cases r with
    | zero =>
      simp only [shapeAdd, shapeRemovable]
      refine ⟨by omega, ?_⟩
      intro n hn
      have hmem : n ∈ M := List.mem_of_mem_head? hn
      have := hm n hmem
      omega
    | succ r =>
      exact ih hM r (by simpa using hr)

theorem shapeRemovable_addBox {d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ)
    (r : Fin d) : shapeRemovable (List.ofFn (addBox μ r)) r.val := by
  rw [← shapeAdd_ofFn]
  exact shapeRemovable_shapeAdd _
    (List.pairwise_ofFn.mpr (fun _ _ h => hμ h.le)) _ (by simp)

end Cloning.YoungGeneral
