import Cloning.TensorHighestGramIsometry
import Cloning.TensorCyclicSectorOperators

/-! The exact Gram isometry intertwines all literal physical generators. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

/-- Linear extension of the universal exact matrix-unit action on words. -/
def formalGenerator (mu : Fin d → ℂ) (a b : Fin d) :
    FormalLowering d →ₗ[ℂ] FormalLowering d :=
  Finsupp.linearCombination ℂ (highestAction mu a b)

theorem formalRealization_formalGenerator
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (f : FormalLowering d) :
    formalRealization Ω (formalGenerator mu a b f) =
      collectiveGenerator n a b (formalRealization Ω f) := by
  change formalRealization Ω
    (∑ w ∈ f.support, f w • highestAction mu a b w) = _
  simp only [map_sum, map_smul, formalRealization_highestAction Ω mu hweight hraise]
  simp only [formalRealization, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]

/-- The cyclic equivalence is an exact intertwiner on the entire cyclic sector,
not merely an asymptotic agreement on selected PBW vectors. -/
theorem highestCyclicIsometry_intertwines
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (a b : Fin d) (x : cyclicSector Ω) :
    highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
        (cyclicGenerator Ω mu hΩweight hΩraise a b x) =
      cyclicGenerator Ψ mu hΨweight hΨraise a b
        (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm x) := by
  obtain ⟨f, hf⟩ : ∃ f : FormalLowering d, formalRealization Ω f = (x : TensorRegister n (Fin d)) := by
    have hx : (x : TensorRegister n (Fin d)) ∈ LinearMap.range (formalRealization Ω) := by
      simpa only [range_formalRealization] using x.property
    exact hx
  have hfmem : formalRealization Ω f ∈ cyclicSector Ω := by
    rw [hf]
    exact x.property
  have hxeq : x = ⟨formalRealization Ω f, hfmem⟩ := Subtype.ext hf.symm
  subst x
  have hfgmem : formalRealization Ω (formalGenerator mu a b f) ∈ cyclicSector Ω := by
    rw [formalRealization_formalGenerator Ω mu hΩweight hΩraise]
    exact cyclicSector_generator_invariant Ω mu hΩweight hΩraise a b hfmem
  have hgen : cyclicGenerator Ω mu hΩweight hΩraise a b
      ⟨formalRealization Ω f, hfmem⟩ =
      ⟨formalRealization Ω (formalGenerator mu a b f), hfgmem⟩ := by
    apply Subtype.ext
    exact (formalRealization_formalGenerator Ω mu hΩweight hΩraise a b f).symm
  rw [hgen]
  apply Subtype.ext
  simp only [highestCyclicIsometry_formalRealization, cyclicGenerator_coe_apply]
  exact formalRealization_formalGenerator Ψ mu hΨweight hΨraise a b f

end Cloning.TensorLie
