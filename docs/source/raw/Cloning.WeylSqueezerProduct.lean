import Cloning.WeylMultimodeDisplacement
import Cloning.MultimodeIdler

/-! Actual tensor products and occupation reindexing of multimode Fock
vectors. No factorization or tensor-product isometry is assumed. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology ENNReal
namespace Cloning.WeylSqueezerProduct
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
abbrev Occupation (d : ℕ) := Fin d → ℕ
abbrev JointFock (a b : ℕ) := lp (fun _ : Occupation a × Occupation b => ℂ) 2
variable {a b : ℕ}

def occupationSplit (a b : ℕ) : Occupation (a+b) ≃ Occupation a × Occupation b where
  toFun k := (fun i => k (Fin.castAdd b i), fun j => k (Fin.natAdd a j))
  invFun p := Fin.append p.1 p.2
  left_inv k := Fin.append_castAdd_natAdd
  right_inv p := by ext <;> simp

def jointNumberBasis (a b : ℕ) : HilbertBasis (Occupation a × Occupation b) ℂ (JointFock a b) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (JointFock a b))

@[simp] theorem jointNumberBasis_apply (p : Occupation a × Occupation b) :
    jointNumberBasis a b p=lp.single 2 p 1 := (jointNumberBasis a b |>.repr_symm_single p).symm

def splitNumberBasis (a b : ℕ) : HilbertBasis (Occupation (a+b)) ℂ (JointFock a b) :=
  HilbertBasis.mk ((jointNumberBasis a b).orthonormal.comp (occupationSplit a b)
    (occupationSplit a b).injective) (by
      simp only [Function.comp_def]
      rw [show Set.range (fun k => jointNumberBasis a b (occupationSplit a b k)) =
          Set.range (jointNumberBasis a b) from
        (occupationSplit a b).surjective.range_comp (jointNumberBasis a b)]
      exact (jointNumberBasis a b).dense_span.ge)

/-- The exact unitary between paired occupations and appended mode lists. -/
def jointReindex (a b : ℕ) : JointFock a b ≃ₗᵢ[ℂ] Fock (a+b) := (splitNumberBasis a b).repr

@[simp] theorem jointReindex_apply (x : JointFock a b) (k : Occupation (a+b)) :
    jointReindex a b x k=x (occupationSplit a b k) := by
  rw [jointReindex, HilbertBasis.repr_apply_apply]
  change ⟪splitNumberBasis a b k,x⟫_ℂ=_
  rw [splitNumberBasis, HilbertBasis.coe_mk]
  simp only [Function.comp_apply, jointNumberBasis_apply, lp.inner_single_left,
    RCLike.inner_apply, map_one, mul_one]

@[simp] theorem jointReindex_symm_apply (x : Fock (a+b)) (p : Occupation a × Occupation b) :
    (jointReindex a b).symm x p=x (Fin.append p.1 p.2) := by
  have h := jointReindex_apply ((jointReindex a b).symm x) (Fin.append p.1 p.2)
  simpa only [LinearIsometryEquiv.apply_symm_apply, occupationSplit, Equiv.coe_fn_mk,
    Fin.append_left, Fin.append_right] using h.symm

theorem product_norm_sq_hasSum (x : Fock a) (y : Fock b) :
    HasSum (fun p : Occupation a × Occupation b => ‖x p.1*y p.2‖^(2:ℕ))
      (‖x‖^2*‖y‖^2) := by
  have hx : HasSum (fun k => ‖x k‖^(2:ℕ)) (‖x‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) x
  have hy : HasSum (fun k => ‖y k‖^(2:ℕ)) (‖y‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) y
  simpa only [norm_mul,mul_pow] using hx.mul hy
    (summable_mul_of_summable_norm hx.summable.norm hy.summable.norm)

/-- Literal coefficient product in the paired occupation Hilbert space. -/
def jointTensor (x : Fock a) (y : Fock b) : JointFock a b := by
  refine ⟨fun p => x p.1*y p.2,memℓp_gen ?_⟩
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (product_norm_sq_hasSum x y).summable

@[simp] theorem jointTensor_apply (x : Fock a) (y : Fock b) (p : Occupation a × Occupation b) :
    jointTensor x y p=x p.1*y p.2 := rfl

theorem jointTensor_norm (x : Fock a) (y : Fock b) : ‖jointTensor x y‖=‖x‖*‖y‖ := by
  have h : ‖jointTensor x y‖^2=(‖x‖*‖y‖)^2 := by
    calc
      _ = ∑' p : Occupation a × Occupation b, ‖x p.1*y p.2‖^(2:ℕ) := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two,jointTensor_apply] using
          lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (jointTensor x y)
      _ = ‖x‖^2*‖y‖^2 := (product_norm_sq_hasSum x y).tsum_eq
      _ = _ := (mul_pow _ _ _).symm
  nlinarith [norm_nonneg (jointTensor x y),mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem jointTensor_inner (x x' : Fock a) (y y' : Fock b) :
    ⟪jointTensor x y,jointTensor x' y'⟫_ℂ=⟪x,x'⟫_ℂ*⟪y,y'⟫_ℂ := by
  have he (p : Occupation a × Occupation b) :
      ⟪jointTensor x y p,jointTensor x' y' p⟫_ℂ=⟪x p.1,x' p.1⟫_ℂ*⟪y p.2,y' p.2⟫_ℂ := by
    simp only [jointTensor_apply,RCLike.inner_apply,map_mul]
    ring
  have hfull : HasSum (fun p : Occupation a × Occupation b =>
      ⟪x p.1,x' p.1⟫_ℂ*⟪y p.2,y' p.2⟫_ℂ) ⟪jointTensor x y,jointTensor x' y'⟫_ℂ := by
    simpa only [he] using lp.hasSum_inner (𝕜 := ℂ) (jointTensor x y) (jointTensor x' y')
  have hout : HasSum (fun i => ⟪x i,x' i⟫_ℂ*⟪y,y'⟫_ℂ)
      ⟪jointTensor x y,jointTensor x' y'⟫_ℂ :=
    hfull.prod_fiberwise (fun i => (lp.hasSum_inner (𝕜 := ℂ) y y').mul_left ⟪x i,x' i⟫_ℂ)
  exact hout.unique ((lp.hasSum_inner (𝕜 := ℂ) x x').mul_right ⟪y,y'⟫_ℂ)

def jointTensorRight (y : Fock b) : Fock a →L[ℂ] JointFock a b :=
  LinearMap.mkContinuous
    { toFun := fun x => jointTensor x y
      map_add' := by intro x x'; ext p; simp [add_mul]
      map_smul' := by intro c x; ext p; simp [mul_assoc] }
    ‖y‖ (fun x => by change ‖jointTensor x y‖ ≤ _; rw [jointTensor_norm,mul_comm])

def jointTensorLeft (x : Fock a) : Fock b →L[ℂ] JointFock a b :=
  LinearMap.mkContinuous
    { toFun := jointTensor x
      map_add' := by intro y y'; ext p; simp [mul_add]
      map_smul' := by intro c y; ext p; simp [mul_left_comm] }
    ‖x‖ (fun y => by change ‖jointTensor x y‖ ≤ _; rw [jointTensor_norm])

/-- The literal product vector in the appended physical mode register. -/
def tensorVector (x : Fock a) (y : Fock b) : Fock (a+b) := jointReindex a b (jointTensor x y)

@[simp] theorem tensorVector_apply (x : Fock a) (y : Fock b) (k : Occupation (a+b)) :
    tensorVector x y k=x (fun i => k (Fin.castAdd b i))*y (fun j => k (Fin.natAdd a j)) := by
  rw [tensorVector,jointReindex_apply,jointTensor_apply]
  rfl

theorem tensorVector_norm (x : Fock a) (y : Fock b) : ‖tensorVector x y‖=‖x‖*‖y‖ := by
  rw [tensorVector,(jointReindex a b).norm_map,jointTensor_norm]

theorem tensorVector_inner (x x' : Fock a) (y y' : Fock b) :
    ⟪tensorVector x y,tensorVector x' y'⟫_ℂ=⟪x,x'⟫_ℂ*⟪y,y'⟫_ℂ := by
  rw [tensorVector,tensorVector,(jointReindex a b).inner_map_map,jointTensor_inner]

def tensorRight (y : Fock b) : Fock a →L[ℂ] Fock (a+b) :=
  (jointReindex a b).toLinearIsometry.toContinuousLinearMap.comp (jointTensorRight y)

def tensorLeft (x : Fock a) : Fock b →L[ℂ] Fock (a+b) :=
  (jointReindex a b).toLinearIsometry.toContinuousLinearMap.comp (jointTensorLeft x)

@[simp] theorem tensorRight_apply (y : Fock b) (x : Fock a) : tensorRight y x=tensorVector x y := rfl
@[simp] theorem tensorLeft_apply (x : Fock a) (y : Fock b) : tensorLeft x y=tensorVector x y := rfl

end Cloning.WeylSqueezerProduct
