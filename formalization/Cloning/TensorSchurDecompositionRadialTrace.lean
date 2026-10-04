import Cloning.TensorSchurDecompositionCharacter
import Mathlib.Algebra.MvPolynomial.Funext

/-! Polynomial cyclic trace identities for the literal physical root operators. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT MvPolynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Denominator-free conjugation by the actual diagonal tensor power. -/
theorem tensorOperator_diagonal_generator_weight (D : Fin d → ℂ) (a b : Fin d) :
    D b • (tensorOperator n (Matrix.diagonal D) * collectiveGenerator n a b) =
      D a • (collectiveGenerator n a b * tensorOperator n (Matrix.diagonal D)) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, tensorOperator_diagonal_apply,
    collectiveGenerator_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : v t = a
  · simp only [if_pos ht]
    have hu : (∏ s, D (Function.update v t b s)) =
        D b * ∏ s ∈ Finset.univ.erase t, D (v s) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun s => D (Function.update v t b s)) (Finset.mem_univ t)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro s hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    have hv : (∏ s, D (v s)) = D a * ∏ s ∈ Finset.univ.erase t, D (v s) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun s => D (v s)) (Finset.mem_univ t), ht]
    rw [hu, hv]
    ring
  · simp [ht]

/-- Moving one root through the weighted physical trace multiplies by the
corresponding coordinate ratio, expressed without any division. -/
theorem tensorWeightTrace_root_cycle
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) (a b : Fin d) :
    X b * tensorWeightTrace (collectiveGenerator n a b * T) =
      X a * tensorWeightTrace (T * collectiveGenerator n a b) := by
  apply MvPolynomial.funext
  intro D
  simp only [map_mul, eval_X, eval_tensorWeightTrace]
  let Q := tensorOperator n (Matrix.diagonal D)
  let E := collectiveGenerator n a b
  have hw : D b • (Q * E) = D a • (E * Q) := tensorOperator_diagonal_generator_weight D a b
  calc
    _ = LinearMap.trace ℂ (TensorRegister n (Fin d)) ((D b • (Q * E)) * T).toLinearMap := by
      rw [smul_mul_assoc]
      change D b * LinearMap.trace ℂ _ (Q.toLinearMap * (E.toLinearMap * T.toLinearMap)) =
        LinearMap.trace ℂ _ (D b • ((Q.toLinearMap * E.toLinearMap) * T.toLinearMap))
      rw [map_smul, smul_eq_mul, mul_assoc]
    _ = LinearMap.trace ℂ (TensorRegister n (Fin d)) ((D a • (E * Q)) * T).toLinearMap := by rw [hw]
    _ = D a * LinearMap.trace ℂ (TensorRegister n (Fin d)) ((E * Q) * T).toLinearMap := by
      rw [smul_mul_assoc]
      change LinearMap.trace ℂ _ (D a • (E.toLinearMap * Q.toLinearMap * T.toLinearMap)) = _
      rw [map_smul, smul_eq_mul]
      rfl
    _ = _ := by
      congr 1
      change LinearMap.trace ℂ _ (E.toLinearMap * (Q.toLinearMap * T.toLinearMap)) =
        LinearMap.trace ℂ _ ((Q.toLinearMap * T.toLinearMap) * E.toLinearMap)
      exact LinearMap.trace_mul_comm ℂ _ _

/-- The full Casimir weighted trace is the actual scalar times the physical
character polynomial. -/
theorem tensorWeightTrace_casimir
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℂ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = mu a • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    tensorWeightTrace (collectiveCasimir n d * (cyclicSector Ω).starProjection) =
      casimirEigenvalue mu • physicalCharacterPolynomial Ω := by
  have he : collectiveCasimir n d * (cyclicSector Ω).starProjection =
      casimirEigenvalue mu • (cyclicSector Ω).starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    exact collectiveCasimir_eq_smul_on_cyclicSector Ω mu hweight hraise
      (Submodule.starProjection_apply_mem _ x)
  rw [he, map_smul, physicalCharacterPolynomial]

theorem tensorWeightTrace_root_difference
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) (a b : Fin d) :
    tensorWeightTrace (collectiveGenerator n a b * collectiveGenerator n b a * T) -
      tensorWeightTrace (collectiveGenerator n b a * collectiveGenerator n a b * T) =
      X a * pderiv a (tensorWeightTrace T) - X b * pderiv b (tensorWeightTrace T) := by
  rw [euler_tensorWeightTrace, euler_tensorWeightTrace, ← map_sub, ← map_sub, ← sub_mul,
    collectiveGenerator_commutator]
  simp only [if_true, sub_mul]

/-- A root-pair contribution satisfies the genuine denominator-free radial
identity; commutation with the projector is the only restriction needed. -/
theorem tensorWeightTrace_root_pair
    (T : TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d)) (a b : Fin d)
    (hT : T * collectiveGenerator n a b = collectiveGenerator n a b * T) :
    (X a - X b) *
      (tensorWeightTrace (collectiveGenerator n a b * collectiveGenerator n b a * T) +
        tensorWeightTrace (collectiveGenerator n b a * collectiveGenerator n a b * T)) =
      (X a + X b) *
        (X a * pderiv a (tensorWeightTrace T) - X b * pderiv b (tensorWeightTrace T)) := by
  have hc := tensorWeightTrace_root_cycle (collectiveGenerator n b a * T) a b
  rw [← mul_assoc, mul_assoc (collectiveGenerator n b a) T, hT,
    ← mul_assoc] at hc
  have hd := tensorWeightTrace_root_difference T a b
  rw [← hd]
  linear_combination -2 * hc

end Cloning.TensorLie
