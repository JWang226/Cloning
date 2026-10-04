import Cloning.TensorFlatProjectorLaw

/-! Literal coordinate inclusions of finite physical tensor registers. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The genuine Hilbert-space embedding induced by an injection of basis labels. -/
def registerEmbedding (ι : A ↪ B) : Register A →ₗᵢ[ℂ] Register B :=
  (((registerBasis B).orthonormal.comp ι ι.injective).orthogonalFamily).linearIsometry

@[simp] theorem registerEmbedding_basis (ι : A ↪ B) (a : A) :
    registerEmbedding ι (registerBasis A a) = registerBasis B (ι a) := by
  rw [registerBasis_apply, registerEmbedding, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

@[simp] theorem registerEmbedding_single (ι : A ↪ B) (a : A) :
    registerEmbedding ι (lp.single 2 a 1) = lp.single 2 (ι a) 1 := by
  simpa only [registerBasis_apply] using registerEmbedding_basis ι a

/-- Every coefficient is the actual zero extension along the injection. -/
theorem registerEmbedding_apply (ι : A ↪ B) (x : Register A) (b : B) :
    registerEmbedding ι x b = ∑ a : A, if ι a = b then x a else 0 := by
  rw [← (registerBasis A).toOrthonormalBasis.sum_repr x, map_sum]
  simp only [map_smul, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    HilbertBasis.coe_toOrthonormalBasis, OrthonormalBasis.repr_apply_apply,
    registerEmbedding_basis, registerBasis_apply, registerEmbedding_single, register_inner_single,
    lp.single_apply, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

@[simp] theorem registerEmbedding_apply_image (ι : A ↪ B) (x : Register A) (a : A) :
    registerEmbedding ι x (ι a) = x a := by
  rw [registerEmbedding_apply]
  simp [ι.injective.eq_iff]

theorem registerEmbedding_apply_not_mem (ι : A ↪ B) (x : Register A) (b : B)
    (hb : b ∉ Set.range ι) : registerEmbedding ι x b = 0 := by
  rw [registerEmbedding_apply]
  apply Finset.sum_eq_zero
  intro a _
  simp only [if_neg (fun h => hb ⟨a,h⟩)]

@[simp] theorem registerEmbedding_adjoint_apply (ι : A ↪ B) (y : Register B) (a : A) :
    (registerEmbedding ι).toContinuousLinearMap.adjoint y a = y (ι a) := by
  rw [← register_inner_single]
  change ⟪lp.single 2 a 1, (registerEmbedding ι).toContinuousLinearMap.adjoint y⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪registerEmbedding ι (lp.single 2 a 1), y⟫_ℂ = _
  rw [registerEmbedding_single, register_inner_single]

/-- A matrix unit replaces exactly one letter of a computational word. -/
theorem slotGenerator_basis {n : ℕ} (t : Fin n) (a b : A) (v : Fin n → A) :
    slotGenerator t a b (registerBasis _ v) =
      if v t = b then registerBasis _ (Function.update v t a) else 0 := by
  by_cases hv : v t = b
  · rw [if_pos hv]
    ext w
    rw [slotGenerator_apply]
    by_cases hw : w = Function.update v t a
    · subst w
      have he : Function.update (Function.update v t a) t b = v := by
        rw [Function.update_idem, ← hv, Function.update_eq_self]
      simp only [registerBasis_apply, lp.single_apply, Function.update_self, if_true,
        Pi.single_eq_same]
      rw [he]
      simp
    · have he : w t = a → Function.update w t b ≠ v := by
        intro ha heq
        have hu := (update_relation t a b w v).mp ⟨ha,heq.symm⟩
        exact hw hu.2
      by_cases ha : w t = a
      · simp [ha, registerBasis_apply, lp.single_apply, he ha, hw]
      · have hw' : Function.update v t a ≠ w := Ne.symm hw
        simp [ha, registerBasis_apply, lp.single_apply, hw, hw']
  · rw [if_neg hv]
    ext w
    have he : Function.update w t b ≠ v := by
      intro h
      have hh := congrFun h t
      exact hv (by simpa using hh.symm)
    simp [slotGenerator_apply, registerBasis_apply, lp.single_apply, he]

/-- The coordinate embedding on the literal tensor word basis. -/
def coordinateWordEmbedding (n r k : ℕ) : (Fin n → Fin r) ↪ (Fin n → Fin (r+k)) where
  toFun v := fun t => Fin.castAdd k (v t)
  inj' v w h := by
    funext t
    apply Fin.ext
    exact congrArg (fun z : Fin (r+k) => z.val) (congrFun h t)

def coordinateTensorEmbedding (n r k : ℕ) :
    TensorRegister n (Fin r) →ₗᵢ[ℂ] TensorRegister n (Fin (r+k)) :=
  registerEmbedding (coordinateWordEmbedding n r k)

@[simp] theorem coordinateTensorEmbedding_basis (n r k : ℕ) (v : Fin n → Fin r) :
    coordinateTensorEmbedding n r k (registerBasis _ v) =
      registerBasis _ (fun t => Fin.castAdd k (v t)) := registerEmbedding_basis _ _

end Cloning.TensorLie
