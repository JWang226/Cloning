import Cloning.TensorLieRelations

/-! The actual cyclic lowering-word filtration of an arbitrary highest tensor.
All positive roots are included. Raising invariance follows from the literal
matrix-unit commutator, without PBW independence or irreducibility. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

abbrev PositiveRoot (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

def PositiveRoot.height (a : PositiveRoot d) : ℕ := a.val.2.val - a.val.1.val

theorem PositiveRoot.height_pos (a : PositiveRoot d) : 0 < a.height := by
  have := a.property
  simp only [PositiveRoot.height]
  omega

noncomputable def loweringHeight : List (PositiveRoot d) → ℕ
  | [] => 0
  | a :: w => a.height + loweringHeight w

noncomputable def loweringWord (Ω : TensorRegister n (Fin d)) :
    List (PositiveRoot d) → TensorRegister n (Fin d)
  | [] => Ω
  | a :: w => collectiveGenerator n a.val.2 a.val.1 (loweringWord Ω w)

def cyclicCutoff (Ω : TensorRegister n (Fin d)) (r : ℤ) :
    Submodule ℂ (TensorRegister n (Fin d)) :=
  Submodule.span ℂ {x | ∃ w : List (PositiveRoot d), (loweringHeight w : ℤ) ≤ r ∧
    x = loweringWord Ω w}

theorem loweringWord_mem_cyclicCutoff (Ω : TensorRegister n (Fin d))
    (w : List (PositiveRoot d)) {r : ℤ} (hr : (loweringHeight w : ℤ) ≤ r) :
    loweringWord Ω w ∈ cyclicCutoff Ω r :=
  Submodule.subset_span ⟨w, hr, rfl⟩

theorem cyclicCutoff_monotone (Ω : TensorRegister n (Fin d)) : Monotone (cyclicCutoff Ω) := by
  intro r s hrs
  apply Submodule.span_mono
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans hrs, rfl⟩

theorem highest_mem_cyclicCutoff_zero (Ω : TensorRegister n (Fin d)) : Ω ∈ cyclicCutoff Ω 0 :=
  loweringWord_mem_cyclicCutoff Ω [] (by simp [loweringHeight])

theorem cyclicCutoff_eq_bot_of_neg (Ω : TensorRegister n (Fin d)) {r : ℤ} (hr : r < 0) :
    cyclicCutoff Ω r = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, rfl⟩
  have := Int.natCast_nonneg (loweringHeight w)
  omega

theorem cyclicCutoff_map_of_words (Ω : TensorRegister n (Fin d))
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) (r s : ℤ)
    (h : ∀ w, (loweringHeight w : ℤ) ≤ r → T (loweringWord Ω w) ∈ cyclicCutoff Ω s)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) :
    T x ∈ cyclicCutoff Ω s := by
  have hh : cyclicCutoff Ω r ≤ (cyclicCutoff Ω s).comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    exact h w hw
  exact hh hx

theorem lowering_mem_cyclicCutoff (Ω : TensorRegister n (Fin d))
    (a : PositiveRoot d) (r : ℤ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) :
    collectiveGenerator n a.val.2 a.val.1 x ∈ cyclicCutoff Ω (r + a.height) := by
  apply cyclicCutoff_map_of_words Ω _ r (r + a.height) _ hx
  intro w hw
  apply loweringWord_mem_cyclicCutoff Ω (a :: w)
  simp only [loweringHeight, Nat.cast_add]
  omega

/-- The Lie commutator gives every root its exact height shift on each actual
lowering word. The Cartan and raising premises concern only the highest tensor. -/
theorem generator_loweringWord_mem
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (w : List (PositiveRoot d)) (a b : Fin d) :
    collectiveGenerator n a b (loweringWord Ω w) ∈
      cyclicCutoff Ω ((loweringHeight w : ℤ) + a.val - b.val) := by
  induction w generalizing a b with
  | nil =>
      simp only [loweringWord, loweringHeight, Nat.cast_zero, zero_add]
      rcases lt_trichotomy a b with hab | hab | hab
      · rw [hraise a b hab]
        exact (cyclicCutoff Ω _).zero_mem
      · subst b
        simp only [sub_self, hweight]
        exact (cyclicCutoff Ω 0).smul_mem _ (highest_mem_cyclicCutoff_zero Ω)
      · let c : PositiveRoot d := ⟨(b, a), hab⟩
        have hh := loweringWord_mem_cyclicCutoff Ω [c] (le_refl ((loweringHeight [c] : ℕ) : ℤ))
        have hc : (loweringHeight [c] : ℤ) = (a.val : ℤ) - b.val := by
          simp only [loweringHeight, PositiveRoot.height, Nat.add_zero, c]
          rw [Int.natCast_sub (Nat.le_of_lt hab)]
        simpa only [loweringWord, hc] using hh
  | cons c w ih =>
      have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) =>
        T (loweringWord Ω w)) (collectiveGenerator_commutator (n := n) a b c.val.2 c.val.1)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] at he
      have he' : collectiveGenerator n a b (loweringWord Ω (c :: w)) =
          collectiveGenerator n c.val.2 c.val.1
            (collectiveGenerator n a b (loweringWord Ω w)) +
          ((if b = c.val.2 then collectiveGenerator n a c.val.1 else 0)
            (loweringWord Ω w) -
          (if c.val.1 = a then collectiveGenerator n c.val.2 b else 0)
            (loweringWord Ω w)) := by
        change _ - _ = _ at he
        simpa only [loweringWord] using (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
      rw [he']
      apply (cyclicCutoff Ω _).add_mem
      · have hh := lowering_mem_cyclicCutoff Ω c _ (ih a b)
        convert hh using 1 <;> simp only [loweringHeight, Nat.cast_add] <;> ring
      · apply (cyclicCutoff Ω _).sub_mem
        · split_ifs with hb
          · subst b
            have hh := ih a c.val.1
            convert hh using 1
            simp only [loweringHeight, Nat.cast_add, PositiveRoot.height]
            rw [Int.natCast_sub (Nat.le_of_lt c.property)]
            ring
          · exact (cyclicCutoff Ω _).zero_mem
        · split_ifs with ha
          · subst a
            have hh := ih c.val.2 b
            convert hh using 1
            simp only [loweringHeight, Nat.cast_add, PositiveRoot.height]
            rw [Int.natCast_sub (Nat.le_of_lt c.property)]
            ring
          · exact (cyclicCutoff Ω _).zero_mem

theorem generator_mem_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (r : ℤ) (a b : Fin d) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) :
    collectiveGenerator n a b x ∈ cyclicCutoff Ω (r + a.val - b.val) := by
  apply cyclicCutoff_map_of_words Ω _ r _ _ hx
  intro w hw
  exact cyclicCutoff_monotone Ω (by omega) (generator_loweringWord_mem Ω mu hweight hraise w a b)

/-- Raising annihilates the full cyclic vacuum cutoff, not merely the chosen vector. -/
theorem raising_zero_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a < b) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω 0) : collectiveGenerator n a b x = 0 := by
  have hh := generator_mem_cyclicCutoff Ω mu hweight hraise 0 a b hx
  rw [cyclicCutoff_eq_bot_of_neg Ω (by have : a.val < b.val := hab; omega)] at hh
  exact hh

/-- Every raising root strictly lowers this filtration. -/
theorem raising_lowers_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a < b) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω (r + 1)) : collectiveGenerator n a b x ∈ cyclicCutoff Ω r := by
  have hh := generator_mem_cyclicCutoff Ω mu hweight hraise (r + 1) a b hx
  exact cyclicCutoff_monotone Ω (by have : a.val < b.val := hab; omega) hh


theorem loweringHeight_eq_zero_iff (w : List (PositiveRoot d)) :
    loweringHeight w = 0 ↔ w = [] := by
  cases w with
  | nil => simp [loweringHeight]
  | cons a w =>
      have ha := a.height_pos
      simp only [loweringHeight, reduceCtorEq, iff_false]
      omega

/-- The cyclic cutoff zero consists precisely of scalar multiples of the chosen
highest vector; there are no extraneous ambient vectors at this cutoff. -/
theorem cyclicCutoff_zero (Ω : TensorRegister n (Fin d)) :
    cyclicCutoff Ω 0 = Submodule.span ℂ {Ω} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨w, hw, rfl⟩
    have hw0 : loweringHeight w = 0 := by omega
    rw [(loweringHeight_eq_zero_iff w).mp hw0, loweringWord]
    exact Submodule.subset_span (Set.mem_singleton Ω)
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = Ω := by simpa only [Set.mem_singleton_iff] using hx
    rw [he]
    exact highest_mem_cyclicCutoff_zero Ω

theorem cyclicCutoff_nat_monotone (Ω : TensorRegister n (Fin d)) :
    Monotone (fun r : ℕ => cyclicCutoff Ω (r : ℤ)) :=
  fun _ _ h => cyclicCutoff_monotone Ω (Int.ofNat_le.mpr h)

theorem lowering_raises_cyclicCutoff (Ω : TensorRegister n (Fin d))
    (a : PositiveRoot d) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω r) :
    collectiveGenerator n a.val.2 a.val.1 x ∈ cyclicCutoff Ω ((r + d : ℕ) : ℤ) := by
  have hh := lowering_mem_cyclicCutoff Ω a r hx
  apply cyclicCutoff_monotone Ω _ hh
  have ha := a.val.2.isLt
  simp only [PositiveRoot.height, Nat.cast_add]
  omega

end Cloning.TensorLie
