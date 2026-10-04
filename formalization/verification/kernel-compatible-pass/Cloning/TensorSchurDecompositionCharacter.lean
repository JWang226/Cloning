import Cloning.TensorSchurDecompositionCasimir
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! A polynomial character obtained from the actual physical sector projector,
and its exact Cartan trace calculus. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def occupancyExponent (v : Fin n → Fin d) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (occupancy v)

@[simp] theorem occupancyExponent_apply (v : Fin n → Fin d) (a : Fin d) :
    occupancyExponent v a = occupancy v a := rfl

/-- Polynomial trace of a physical operator against the diagonal tensor power. -/
def tensorWeightTrace : (TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) →ₗ[ℂ]
    MvPolynomial (Fin d) ℂ where
  toFun T := ∑ v : Fin n → Fin d, monomial (occupancyExponent v) (T (registerBasis _ v) v)
  map_add' T U := by simp [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c T := by
    simp [ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
      Finset.smul_sum, smul_monomial]

@[simp] theorem tensorWeightTrace_apply
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) :
    tensorWeightTrace T = ∑ v : Fin n → Fin d,
      monomial (occupancyExponent v) (T (registerBasis _ v) v) := rfl

/-- The physical character is defined from the actual orthogonal projector. -/
def physicalCharacterPolynomial (Ω : TensorRegister n (Fin d)) : MvPolynomial (Fin d) ℂ :=
  tensorWeightTrace (cyclicSector Ω).starProjection

/-- Coordinate Euler differentiation is actual multiplication by a Cartan
matrix unit inside the weighted trace. -/
theorem euler_tensorWeightTrace
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) (a : Fin d) :
    X a * pderiv a (tensorWeightTrace T) =
      tensorWeightTrace (collectiveGenerator n a a * T) := by
  simp only [tensorWeightTrace_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [X_mul_pderiv_monomial]
  rw [smul_monomial]
  simp only [occupancyExponent_apply, ContinuousLinearMap.mul_apply,
    collectiveGenerator_diagonal, nsmul_eq_mul]

/-- Evaluation is the literal finite-dimensional trace of the tensor operator. -/
theorem eval_tensorWeightTrace (D : Fin d → ℂ)
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) :
    eval D (tensorWeightTrace T) = LinearMap.trace ℂ (TensorRegister n (Fin d))
      (tensorOperator n (Matrix.diagonal D) * T).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (registerBasis (Fin n → Fin d)).toOrthonormalBasis]
  simp only [tensorWeightTrace_apply, map_sum, eval_monomial, HilbertBasis.coe_toOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [occupancyExponent_apply]
  change T (registerBasis _ v) v * (∏ a, D a ^ occupancy v a) =
    ⟪registerBasis _ v, tensorOperator n (Matrix.diagonal D) (T (registerBasis _ v))⟫_ℂ
  rw [registerBasis_apply, register_inner_single, tensorOperator_diagonal_apply]
  have he : (∏ a, D a ^ occupancy v a) = ∏ t, D (v t) := by
    simpa [occupancy, Fintype.card_subtype] using Fintype.prod_fiberwise' v D
  rw [he, mul_comm]

theorem eval_physicalCharacterPolynomial
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (D : Fin d → ℂ) :
    eval D (physicalCharacterPolynomial Ω) =
      LinearMap.trace ℂ (cyclicSector Ω)
        (cyclicTensorOperator Ω mu hweight hraise (Matrix.diagonal D)).toLinearMap := by
  rw [physicalCharacterPolynomial, eval_tensorWeightTrace]
  let S := cyclicSector Ω
  let A := cyclicTensorOperator Ω mu hweight hraise (Matrix.diagonal D)
  have he : (tensorOperator n (Matrix.diagonal D) * S.starProjection).toLinearMap =
      (S.subtype.comp A.toLinearMap).comp S.orthogonalProjection.toLinearMap := rfl
  rw [he, LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change S.starProjection (A x) = (A x : TensorRegister n (Fin d))
  exact Submodule.starProjection_eq_self_iff.mpr (A x).property

/-- Specialization identifies the polynomial with the actual positive-sector
partition function, independently of any Weyl formula. -/
theorem eval_physicalCharacterPolynomial_nonneg
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) :
    (eval (fun a => (p a : ℂ)) (physicalCharacterPolynomial Ω)).re =
      sectorPartitionFunction Ω mu hweight hraise p := by
  rw [eval_physicalCharacterPolynomial Ω (fun a => (mu a : ℂ)) hweight hraise]
  exact (sectorPartitionFunction_eq_linearMapTrace Ω mu hweight hraise p hp).symm

/-- Every nonzero coefficient comes from an actual supported computational
weight; hence it is dominated by the physical highest partition. -/
theorem physicalCharacterPolynomial_support_dominated
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (m : Fin d →₀ ℕ) (hm : coeff m (physicalCharacterPolynomial Ω) ≠ 0) (R : ℕ) :
    weightPrefix (fun a => (m a : ℤ)) R ≤ weightPrefix (fun a => (mu a : ℤ)) R := by
  classical
  have hv : ∃ v : Fin n → Fin d, occupancyExponent v = m ∧
      (cyclicSector Ω).starProjection (registerBasis _ v) v ≠ 0 := by
    by_contra! hh
    apply hm
    simp only [physicalCharacterPolynomial, tensorWeightTrace_apply, coeff_sum]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hvm : occupancyExponent v = m
    · simp only [coeff_monomial, hvm, if_true]
      exact hh v hvm
    · simp [coeff_monomial, hvm]
  obtain ⟨v, rfl, hv⟩ := hv
  exact cyclicSector_occupancy_dominated Ω mu hweight
    (Submodule.starProjection_apply_mem _ _) v hv R

end Cloning.TensorLie
