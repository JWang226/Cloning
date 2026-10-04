import Cloning.TensorLieHighestWeight

/-! Literal tensor concatenation, its Hilbert norm, and the collective Lie
generator product rule. These apply to arbitrary register vectors. -/

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] {n m : ℕ}

def splitWordsEquiv (n m : ℕ) :
    (Fin (n + m) → A) ≃ (Fin n → A) × (Fin m → A) where
  toFun w := (fun i => w (Fin.castAdd m i), fun j => w (Fin.natAdd n j))
  invFun p := Fin.addCases p.1 p.2
  left_inv w := Fin.addCases_castAdd_natAdd w
  right_inv p := by ext <;> simp

def tensorJoin (x : TensorRegister n A) (y : TensorRegister m A) :
    TensorRegister (n + m) A :=
  ⟨fun w => x (fun i => w (Fin.castAdd m i)) * y (fun j => w (Fin.natAdd n j)),
    memℓp_gen (by simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem tensorJoin_apply (x : TensorRegister n A) (y : TensorRegister m A)
    (w : Fin (n + m) → A) :
    tensorJoin x y w =
      x (fun i => w (Fin.castAdd m i)) * y (fun j => w (Fin.natAdd n j)) := rfl

@[simp] theorem tensorJoin_zero_left (y : TensorRegister m A) :
    tensorJoin (0 : TensorRegister n A) y = 0 := by ext; simp

@[simp] theorem tensorJoin_zero_right (x : TensorRegister n A) :
    tensorJoin x (0 : TensorRegister m A) = 0 := by ext; simp

@[simp] theorem tensorJoin_smul_left (c : ℂ) (x : TensorRegister n A)
    (y : TensorRegister m A) : tensorJoin (c • x) y = c • tensorJoin x y := by
  ext; simp [mul_assoc]

@[simp] theorem tensorJoin_smul_right (c : ℂ) (x : TensorRegister n A)
    (y : TensorRegister m A) : tensorJoin x (c • y) = c • tensorJoin x y := by
  ext; simp [mul_left_comm]

theorem tensorJoin_inner (x x' : TensorRegister n A) (y y' : TensorRegister m A) :
    ⟪tensorJoin x y, tensorJoin x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  simp only [lp.inner_eq_tsum, tsum_fintype, RCLike.inner_apply, tensorJoin_apply,
    map_mul]
  change (∑ w, (fun p : (Fin n → A) × (Fin m → A) =>
    (x' p.1 * y' p.2) * (star (x p.1) * star (y p.2)))
    (splitWordsEquiv n m w)) = _
  rw [(splitWordsEquiv (A := A) n m).sum_comp (fun p =>
    (x' p.1 * y' p.2) * (star (x p.1) * star (y p.2)))]
  simp only [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun v w =>
    x' v * y' w * (star (x v) * star (y w)))]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  simp only [starRingEnd_apply]
  ring

theorem tensorJoin_norm (x : TensorRegister n A) (y : TensorRegister m A) :
    ‖tensorJoin x y‖ = ‖x‖ * ‖y‖ := by
  have he := congrArg Complex.re (tensorJoin_inner x x y y)
  rw [Complex.mul_re] at he
  change (RCLike.re : ℂ → ℝ) ⟪tensorJoin x y, tensorJoin x y⟫_ℂ =
    (RCLike.re : ℂ → ℝ) ⟪x, x⟫_ℂ * (RCLike.re : ℂ → ℝ) ⟪y, y⟫_ℂ -
    (RCLike.im : ℂ → ℝ) ⟪x, x⟫_ℂ * (RCLike.im : ℂ → ℝ) ⟪y, y⟫_ℂ at he
  simp only [inner_self_eq_norm_sq, inner_self_im, mul_zero, sub_zero] at he
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hz := norm_nonneg (tensorJoin x y)
  nlinarith [mul_nonneg hx hy]

theorem tensorJoin_norm_one (x : TensorRegister n A) (y : TensorRegister m A)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖tensorJoin x y‖ = 1 := by
  rw [tensorJoin_norm, hx, hy, one_mul]

theorem restrict_update_left (w : Fin (n + m) → A) (t : Fin n) (b : A) :
    (fun i => Function.update w (Fin.castAdd m t) b (Fin.castAdd m i)) =
      Function.update (fun i => w (Fin.castAdd m i)) t b := by
  funext i
  by_cases hi : i = t
  · subst i; simp
  · have hne : Fin.castAdd m i ≠ Fin.castAdd m t := by simpa using hi
    simp [Function.update_of_ne hi, Function.update_of_ne hne]

theorem restrict_update_left_other (w : Fin (n + m) → A) (t : Fin n) (b : A) :
    (fun j => Function.update w (Fin.castAdd m t) b (Fin.natAdd n j)) =
      (fun j => w (Fin.natAdd n j)) := by
  funext j
  apply Function.update_of_ne
  intro he
  have := congrArg Fin.val he
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

theorem restrict_update_right (w : Fin (n + m) → A) (t : Fin m) (b : A) :
    (fun j => Function.update w (Fin.natAdd n t) b (Fin.natAdd n j)) =
      Function.update (fun j => w (Fin.natAdd n j)) t b := by
  funext j
  by_cases hj : j = t
  · subst j; simp
  · have hne : Fin.natAdd n j ≠ Fin.natAdd n t := by simpa using hj
    simp [Function.update_of_ne hj, Function.update_of_ne hne]

theorem restrict_update_right_other (w : Fin (n + m) → A) (t : Fin m) (b : A) :
    (fun i => Function.update w (Fin.natAdd n t) b (Fin.castAdd m i)) =
      (fun i => w (Fin.castAdd m i)) := by
  funext i
  apply Function.update_of_ne
  intro he
  have := congrArg Fin.val he
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

/-- The actual collective matrix-unit generator obeys the tensor product rule. -/
theorem collectiveGenerator_tensorJoin (a b : A)
    (x : TensorRegister n A) (y : TensorRegister m A) :
    collectiveGenerator (n + m) a b (tensorJoin x y) =
      tensorJoin (collectiveGenerator n a b x) y +
      tensorJoin x (collectiveGenerator m a b y) := by
  ext w
  simp only [collectiveGenerator_apply, tensorJoin_apply, lp.coeFn_add, Pi.add_apply,
    Fin.sum_univ_add, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [restrict_update_left, restrict_update_left_other]
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro t ht
    rw [restrict_update_right, restrict_update_right_other]
    split_ifs <;> simp

theorem tensorJoin_raising_zero (a b : A) (x : TensorRegister n A)
    (y : TensorRegister m A) (hx : collectiveGenerator n a b x = 0)
    (hy : collectiveGenerator m a b y = 0) :
    collectiveGenerator (n + m) a b (tensorJoin x y) = 0 := by
  rw [collectiveGenerator_tensorJoin, hx, hy, tensorJoin_zero_left,
    tensorJoin_zero_right, add_zero]

theorem tensorJoin_cartan (a : A) (x : TensorRegister n A) (y : TensorRegister m A)
    (α β : ℂ) (hx : collectiveGenerator n a a x = α • x)
    (hy : collectiveGenerator m a a y = β • y) :
    collectiveGenerator (n + m) a a (tensorJoin x y) = (α + β) • tensorJoin x y := by
  rw [collectiveGenerator_tensorJoin, hx, hy, tensorJoin_smul_left,
    tensorJoin_smul_right, add_smul]

end Cloning.TensorLie
