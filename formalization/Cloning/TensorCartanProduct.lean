import Cloning.TensorCyclicSector
import Cloning.TensorLieProduct

/-! The literal tensor-product subspace of two physical cyclic sectors. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

def tensorProductSector (P : Submodule ℂ (TensorRegister n (Fin d)))
    (Q : Submodule ℂ (TensorRegister m (Fin d))) :
    Submodule ℂ (TensorRegister (n + m) (Fin d)) :=
  Submodule.span ℂ {z | ∃ x ∈ P, ∃ y ∈ Q, z = tensorJoin x y}

theorem tensorJoin_mem_tensorProductSector
    (P : Submodule ℂ (TensorRegister n (Fin d)))
    (Q : Submodule ℂ (TensorRegister m (Fin d)))
    {x : TensorRegister n (Fin d)} (hx : x ∈ P)
    {y : TensorRegister m (Fin d)} (hy : y ∈ Q) :
    tensorJoin x y ∈ tensorProductSector P Q :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem tensorProductSector_generator_invariant
    (P : Submodule ℂ (TensorRegister n (Fin d)))
    (Q : Submodule ℂ (TensorRegister m (Fin d)))
    (hP : ∀ a b x, x ∈ P → collectiveGenerator n a b x ∈ P)
    (hQ : ∀ a b x, x ∈ Q → collectiveGenerator m a b x ∈ Q)
    (a b : Fin d) {z : TensorRegister (n + m) (Fin d)}
    (hz : z ∈ tensorProductSector P Q) :
    collectiveGenerator (n + m) a b z ∈ tensorProductSector P Q := by
  have h : tensorProductSector P Q ≤ (tensorProductSector P Q).comap
      (collectiveGenerator (n + m) a b).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change collectiveGenerator (n + m) a b (tensorJoin x y) ∈ tensorProductSector P Q
    rw [collectiveGenerator_tensorJoin]
    exact (tensorProductSector P Q).add_mem
      (tensorJoin_mem_tensorProductSector P Q (hP a b x hx) hy)
      (tensorJoin_mem_tensorProductSector P Q hx (hQ a b y hy))
  exact h hz

/-- The cyclic sector of the product highest tensor lies inside the actual
tensor-product subspace of the two original sectors. -/
theorem cyclicSector_tensorJoin_le
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu nu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = nu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0) :
    cyclicSector (tensorJoin Ω Ψ) ≤ tensorProductSector (cyclicSector Ω) (cyclicSector Ψ) := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, rfl⟩
  induction w with
  | nil =>
      exact tensorJoin_mem_tensorProductSector _ _
        (highest_mem_cyclicSector Ω) (highest_mem_cyclicSector Ψ)
  | cons c w ih =>
      exact tensorProductSector_generator_invariant _ _
        (fun a b x hx => cyclicSector_generator_invariant Ω mu hΩweight hΩraise a b hx)
        (fun a b x hx => cyclicSector_generator_invariant Ψ nu hΨweight hΨraise a b hx)
        c.val.2 c.val.1 ih

def sectorInclusionIsometry {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {P Q : Submodule ℂ H} (h : P ≤ Q) : P →ₗᵢ[ℂ] Q where
  toLinearMap := Submodule.inclusion h
  norm_map' _ := rfl

end Cloning.TensorLie
