import Cloning.TensorPBWSpanning

/-! Exact dominance support of physical cyclic highest sectors. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def weightPrefix (ν : Fin d → ℤ) (R : ℕ) : ℤ :=
  ∑ a : Fin d with a.val < R, ν a

theorem weightPrefix_add (ν κ : Fin d → ℤ) (R : ℕ) :
    weightPrefix (ν + κ) R = weightPrefix ν R + weightPrefix κ R := by
  simp [weightPrefix, Finset.sum_add_distrib]

@[simp] theorem weightPrefix_zero (R : ℕ) : weightPrefix (0 : Fin d → ℤ) R = 0 := by
  simp [weightPrefix]

theorem PositiveRoot.weightPrefix_eq (a : PositiveRoot d) (R : ℕ) :
    weightPrefix a.weight R =
      (if a.val.2.val < R then 1 else 0) - (if a.val.1.val < R then 1 else 0) := by
  simp [weightPrefix, PositiveRoot.weight, Finset.sum_sub_distrib]

theorem PositiveRoot.weightPrefix_nonpos (a : PositiveRoot d) (R : ℕ) :
    weightPrefix a.weight R ≤ 0 := by
  rw [a.weightPrefix_eq]
  have ha := a.property
  split_ifs <;> omega

theorem loweringWeight_prefix_nonpos (w : List (PositiveRoot d)) (R : ℕ) :
    weightPrefix (loweringWeight w) R ≤ 0 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [loweringWeight_cons, weightPrefix_add]
    exact add_nonpos (a.weightPrefix_nonpos R) ih

/-- Every nonzero computational coefficient of an actual lowering word has
exactly the Cartan weight recorded by its additive root grading. -/
theorem loweringWord_occupancy_eq_weight
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : List (PositiveRoot d)) (v : Fin n → Fin d)
    (hv : loweringWord Ω w v ≠ 0) (a : Fin d) :
    (occupancy v a : ℤ) = (mu a : ℤ) + loweringWeight w a := by
  have he := congrArg (fun x : TensorRegister n (Fin d) => x v)
    (cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight w a)
  simp only [collectiveGenerator_diagonal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
  have he' : (occupancy v a : ℂ) = (mu a : ℂ) + (loweringWeight w a : ℂ) :=
    mul_right_cancel₀ hv he
  apply Int.cast_injective (α := ℂ)
  simpa only [Int.cast_add, Int.cast_natCast] using he'

theorem loweringWord_occupancy_dominated
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : List (PositiveRoot d)) (v : Fin n → Fin d)
    (hv : loweringWord Ω w v ≠ 0) (R : ℕ) :
    weightPrefix (fun a => (occupancy v a : ℤ)) R ≤ weightPrefix (fun a => (mu a : ℤ)) R := by
  have he : (fun a => (occupancy v a : ℤ)) =
      (fun a => (mu a : ℤ)) + loweringWeight w :=
    funext (loweringWord_occupancy_eq_weight Ω mu hweight w v hv)
  rw [he, weightPrefix_add]
  exact add_le_of_nonpos_right (loweringWeight_prefix_nonpos w R)

def dominanceSupport (mu : Fin d → ℕ) : Submodule ℂ (TensorRegister n (Fin d)) where
  carrier := {x | ∀ v R, weightPrefix (fun a => (mu a : ℤ)) R <
    weightPrefix (fun a => (occupancy v a : ℤ)) R → x v = 0}
  zero_mem' := by intro v R _; rfl
  add_mem' := by intro x y hx hy v R hR; simp [hx v R hR, hy v R hR]
  smul_mem' := by intro c x hx v R hR; simp [lp.coeFn_smul, hx v R hR]

theorem cyclicSector_le_dominanceSupport
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    cyclicSector Ω ≤ dominanceSupport mu := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩ v R hR
  by_contra hv
  exact (not_lt_of_ge (loweringWord_occupancy_dominated Ω mu hweight w v hv R)) hR

/-- Full-sector support dominance holds for every vector in the actual cyclic
sector, with no assumptions about an expansion being independent. -/
theorem cyclicSector_occupancy_dominated
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω)
    (v : Fin n → Fin d) (hv : x v ≠ 0) (R : ℕ) :
    weightPrefix (fun a => (occupancy v a : ℤ)) R ≤ weightPrefix (fun a => (mu a : ℤ)) R := by
  by_contra! hR
  exact hv (cyclicSector_le_dominanceSupport Ω mu hweight hx v R hR)

/-- Every actual nonzero joint Cartan eigentensor in the cyclic sector has
weight dominated by the highest weight. -/
theorem cyclicSector_cartanWeight_dominated
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω) (hx0 : x ≠ 0)
    (κ : Fin d → ℕ) (hκ : ∀ a, collectiveGenerator n a a x = (κ a : ℂ) • x)
    (R : ℕ) :
    weightPrefix (fun a => (κ a : ℤ)) R ≤ weightPrefix (fun a => (mu a : ℤ)) R := by
  obtain ⟨v, hv⟩ : ∃ v : Fin n → Fin d, x v ≠ 0 := by
    by_contra! h
    apply hx0
    ext v
    exact h v
  have he : ∀ a, occupancy v a = κ a := by
    intro a
    have hh := congrArg (fun y : TensorRegister n (Fin d) => y v) (hκ a)
    simp only [collectiveGenerator_diagonal, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hh
    have hh' : (occupancy v a : ℂ) = (κ a : ℂ) := mul_right_cancel₀ hv hh
    exact Nat.cast_injective hh'
  simpa only [he] using cyclicSector_occupancy_dominated Ω mu hweight hx v hv R

end Cloning.TensorLie
