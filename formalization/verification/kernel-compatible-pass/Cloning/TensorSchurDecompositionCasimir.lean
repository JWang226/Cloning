import Cloning.TensorSchurDecompositionBounds

/-! The genuine quadratic Casimir on tensor space and its scalar on every
physical highest-weight cyclic sector. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def collectiveCasimir (n d : ℕ) : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  ∑ a : Fin d, ∑ b : Fin d, collectiveGenerator n a b * collectiveGenerator n b a

/-- The quadratic tensor Casimir commutes with every actual matrix unit. -/
theorem collectiveCasimir_commutes (c e : Fin d) :
    collectiveCasimir n d * collectiveGenerator n c e =
      collectiveGenerator n c e * collectiveCasimir n d := by
  let E := fun a b : Fin d => collectiveGenerator n a b
  have hterm (a b : Fin d) :
      E a b * E b a * E c e - E c e * (E a b * E b a) =
        (if a = c then E a b * E b e else 0) -
        (if e = b then E a b * E c a else 0) +
        ((if b = c then E a e * E b a else 0) -
          (if e = a then E c b * E b a else 0)) := by
    calc
      _ = E a b * (E b a * E c e - E c e * E b a) +
          (E a b * E c e - E c e * E a b) * E b a := by noncomm_ring
      _ = _ := by
        rw [collectiveGenerator_commutator, collectiveGenerator_commutator]
        simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
        rfl
  apply sub_eq_zero.mp
  change (∑ a, ∑ b, E a b * E b a) * E c e - E c e * (∑ a, ∑ b, E a b * E b a) = 0
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  noncomm_ring

def casimirEigenvalue (mu : Fin d → ℂ) : ℂ :=
  ∑ a, mu a * mu a + ∑ a, ∑ b, if a < b then mu a - mu b else 0

theorem collectiveCasimir_highest
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    collectiveCasimir n d Ω = casimirEigenvalue mu • Ω := by
  have hterm (a b : Fin d) :
      collectiveGenerator n a b (collectiveGenerator n b a Ω) =
        ((if a = b then mu a * mu a else 0) +
          (if a < b then mu a - mu b else 0)) • Ω := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have h := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T Ω)
        (collectiveGenerator_commutator (n := n) a b b a)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
        if_true, hraise a b hab, map_zero, sub_zero, hweight] at h
      simpa only [if_neg (ne_of_lt hab), if_pos hab, zero_add, sub_smul] using h
    · subst b
      rw [hweight, map_smul, hweight, smul_smul]
      simp
    · rw [hraise b a hab, map_zero]
      simp [ne_of_gt hab, not_lt.mpr hab.le]
  simp only [collectiveCasimir, ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply,
    hterm, ← Finset.sum_smul, casimirEigenvalue]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The scalar extends to the whole literal sector by actual lowering words. -/
theorem collectiveCasimir_eq_smul_on_cyclicSector
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω) :
    collectiveCasimir n d x = casimirEigenvalue mu • x := by
  have hw (w : List (PositiveRoot d)) :
      collectiveCasimir n d (loweringWord Ω w) = casimirEigenvalue mu • loweringWord Ω w := by
    induction w with
    | nil => exact collectiveCasimir_highest Ω mu hweight hraise
    | cons r w ih =>
      change collectiveCasimir n d (collectiveGenerator n r.val.2 r.val.1 (loweringWord Ω w)) = _
      have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) =>
        T (loweringWord Ω w)) (collectiveCasimir_commutes (n := n) r.val.2 r.val.1)
      change collectiveCasimir n d (collectiveGenerator n r.val.2 r.val.1 (loweringWord Ω w)) =
        collectiveGenerator n r.val.2 r.val.1 (collectiveCasimir n d (loweringWord Ω w)) at he
      rw [he, ih, map_smul]
      rfl
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hw w
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | smul c x hx ih => simp only [map_smul, ih, smul_smul, mul_comm]

end Cloning.TensorLie
