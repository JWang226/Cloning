import Cloning.TensorHighestGram
import Cloning.TensorCyclicSector
import Mathlib.LinearAlgebra.Isomorphisms

/-! Exact isometries of physical cyclic highest sectors induced by equal
lowering-word Gram matrices. Quotienting equal realization kernels transports
all linear relations, without assuming a PBW basis. -/
noncomputable section
open scoped InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section RangeIsometry
variable {V H K : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem ker_eq_of_norm_eq (f : V →ₗ[ℂ] H) (g : V →ₗ[ℂ] K)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : LinearMap.ker f = LinearMap.ker g := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [← h x, hx, norm_zero]
  · intro hx
    apply norm_eq_zero.mp
    rw [h x, hx, norm_zero]

def sameNormRangeLinearEquiv (f : V →ₗ[ℂ] H) (g : V →ₗ[ℂ] K)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : LinearMap.range f ≃ₗ[ℂ] LinearMap.range g :=
  f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_eq_of_norm_eq f g h)).trans g.quotKerEquivRange)

theorem sameNormRangeLinearEquiv_apply (f : V →ₗ[ℂ] H) (g : V →ₗ[ℂ] K)
    (h : ∀ x, ‖f x‖ = ‖g x‖) (x : V) (hx : f x ∈ LinearMap.range f) :
    (sameNormRangeLinearEquiv f g h ⟨f x, hx⟩ : K) = g x := by
  simp only [sameNormRangeLinearEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]

def sameNormRangeIsometry (f : V →ₗ[ℂ] H) (g : V →ₗ[ℂ] K)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : LinearMap.range f ≃ₗᵢ[ℂ] LinearMap.range g where
  toLinearEquiv := sameNormRangeLinearEquiv f g h
  norm_map' x := by
    obtain ⟨v, hv⟩ := x.property
    have he : x = ⟨f v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
    rw [he]
    change ‖(sameNormRangeLinearEquiv f g h ⟨f v, _⟩ : K)‖ = ‖f v‖
    rw [sameNormRangeLinearEquiv_apply, h v]

@[simp] theorem sameNormRangeIsometry_apply (f : V →ₗ[ℂ] H) (g : V →ₗ[ℂ] K)
    (h : ∀ x, ‖f x‖ = ‖g x‖) (x : V) (hx : f x ∈ LinearMap.range f) :
    (sameNormRangeIsometry f g h ⟨f x, hx⟩ : K) = g x :=
  sameNormRangeLinearEquiv_apply f g h x hx
end RangeIsometry

variable {n m d : ℕ}

theorem range_formalRealization (Ω : TensorRegister n (Fin d)) :
    LinearMap.range (formalRealization Ω) = cyclicSector Ω :=
  Finsupp.range_linearCombination ℂ

/-- The exact cyclic isometry between any two normalized physical highest
tensors of the same weight. It is defined on their whole cyclic sectors. -/
def highestCyclicIsometry
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1) : cyclicSector Ω ≃ₗᵢ[ℂ] cyclicSector Ψ :=
  (LinearIsometryEquiv.ofEq _ _ (range_formalRealization Ω).symm).trans
    ((sameNormRangeIsometry (formalRealization Ω) (formalRealization Ψ)
      (highest_formalRealization_norm_eq Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm)).trans
      (LinearIsometryEquiv.ofEq _ _ (range_formalRealization Ψ)))

theorem highestCyclicIsometry_formalRealization
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (f : FormalLowering d) (hf : formalRealization Ω f ∈ cyclicSector Ω) :
    (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
      ⟨formalRealization Ω f, hf⟩ : TensorRegister m (Fin d)) = formalRealization Ψ f := by
  change (sameNormRangeIsometry (formalRealization Ω) (formalRealization Ψ)
    (highest_formalRealization_norm_eq Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm)
    ⟨formalRealization Ω f, ⟨f, rfl⟩⟩ : TensorRegister m (Fin d)) = _
  exact sameNormRangeIsometry_apply _ _ _ f _

theorem highestCyclicIsometry_loweringWord
    (Ω : TensorRegister n (Fin d)) (Ψ : TensorRegister m (Fin d))
    (mu : Fin d → ℂ)
    (hΩweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hΨweight : ∀ a, collectiveGenerator m a a Ψ = mu a • Ψ)
    (hΩraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hΨraise : ∀ a b, a < b → collectiveGenerator m a b Ψ = 0)
    (hΩnorm : ‖Ω‖ = 1) (hΨnorm : ‖Ψ‖ = 1)
    (w : List (PositiveRoot d)) :
    (highestCyclicIsometry Ω Ψ mu hΩweight hΨweight hΩraise hΨraise hΩnorm hΨnorm
      ⟨loweringWord Ω w, loweringWord_mem_cyclicSector Ω w⟩ : TensorRegister m (Fin d)) =
      loweringWord Ψ w := by
  have hh := highestCyclicIsometry_formalRealization Ω Ψ mu hΩweight hΨweight
    hΩraise hΨraise hΩnorm hΨnorm (Finsupp.single w 1)
    (by simpa only [formalRealization_single, one_smul] using loweringWord_mem_cyclicSector Ω w)
  simpa only [formalRealization_single, one_smul] using hh

end Cloning.TensorLie
