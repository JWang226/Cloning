import Cloning.TensorCyclicSectorIrreducible

/-! Literal restricted generators and scalarity inside the physical cyclic Hilbert space. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

/-- Restriction of the actual tensor matrix unit to its invariant cyclic sector. -/
def cyclicGenerator (a b : Fin d) : cyclicSector Ω →L[ℂ] cyclicSector Ω :=
  ((collectiveGenerator n a b).comp (cyclicSector Ω).subtypeL).codRestrict
    (cyclicSector Ω) (fun x => cyclicSector_generator_invariant Ω mu hweight hraise a b x.property)

@[simp] theorem cyclicGenerator_coe_apply (a b : Fin d) (x : cyclicSector Ω) :
    (cyclicGenerator Ω mu hweight hraise a b x : TensorRegister n (Fin d)) =
      collectiveGenerator n a b x := rfl

/-- The restricted generators retain the genuine Hilbert adjoint relation. -/
theorem cyclicGenerator_adjoint (a b : Fin d) :
    (cyclicGenerator Ω mu hweight hraise a b).adjoint =
      cyclicGenerator Ω mu hweight hraise b a := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change ⟪collectiveGenerator n b a (x : TensorRegister n (Fin d)),
      (y : TensorRegister n (Fin d))⟫_ℂ =
    ⟪(x : TensorRegister n (Fin d)), collectiveGenerator n a b (y : TensorRegister n (Fin d))⟫_ℂ
  rw [← collectiveGenerator_adjoint b a, ContinuousLinearMap.adjoint_inner_right]

/-- Scalar commutant on the literal sector Hilbert space. -/
theorem cyclicGenerator_commutant_scalar (hΩ : ‖Ω‖ = 1)
    (T : cyclicSector Ω →ₗ[ℂ] cyclicSector Ω)
    (hcomm : ∀ a b x,
      T (cyclicGenerator Ω mu hweight hraise a b x) =
        cyclicGenerator Ω mu hweight hraise a b (T x)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  let S := cyclicSector Ω
  let T' : TensorRegister n (Fin d) →ₗ[ℂ] TensorRegister n (Fin d) :=
    S.subtype.comp (T.comp S.orthogonalProjection.toLinearMap)
  have hproj (x : S) : S.orthogonalProjection x = x := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr x.property
  have hT' (x : S) : T' x = (T x : TensorRegister n (Fin d)) := by
    change (T (S.orthogonalProjection x) : TensorRegister n (Fin d)) = _
    rw [hproj]
  obtain ⟨c, hc⟩ := cyclicSector_commutant_scalar Ω hΩ hraise T'
    (fun x _ => (T (S.orthogonalProjection x)).property) (by
      intro a b x hx
      let xx : S := ⟨x, hx⟩
      have he : T' (collectiveGenerator n a b x) =
          (T (cyclicGenerator Ω mu hweight hraise a b xx) : TensorRegister n (Fin d)) :=
        hT' (cyclicGenerator Ω mu hweight hraise a b xx)
      rw [he, hcomm, cyclicGenerator_coe_apply, hT' xx])
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simpa only [hT' x] using hc x x.property

/-- Restricted operators retain all literal `gl_d` commutators. -/
theorem cyclicGenerator_commutator (a b c e : Fin d) :
    cyclicGenerator Ω mu hweight hraise a b * cyclicGenerator Ω mu hweight hraise c e -
      cyclicGenerator Ω mu hweight hraise c e * cyclicGenerator Ω mu hweight hraise a b =
      (if b = c then cyclicGenerator Ω mu hweight hraise a e else 0) -
        (if e = a then cyclicGenerator Ω mu hweight hraise c b else 0) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have he := congrArg (fun T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) => T x)
    (collectiveGenerator_commutator (n := n) a b c e)
  by_cases hbc : b = c <;> by_cases hea : e = a <;>
    simpa only [hbc, hea, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    cyclicGenerator_coe_apply, Submodule.coe_sub, Submodule.coe_zero, ContinuousLinearMap.zero_apply,
    if_true, if_false] using he

end Cloning.TensorLie
