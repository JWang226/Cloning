import Cloning.TensorCartanIntertwiner
import Cloning.TensorHighestGramCovariance

/-! Literal tensor-power action on the physical product sector and exact
Cartan intertwining for every matrix. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem tensorOperator_tensorJoin {n m : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (x : TensorRegister n (Fin d)) (y : TensorRegister m (Fin d)) :
    tensorOperator (n+m) X (tensorJoin x y) =
      tensorJoin (tensorOperator n X x) (tensorOperator m X y) := by
  ext w
  simp only [tensorOperator_apply, tensorJoin_apply, Fin.prod_univ_add]
  change (∑ v, (fun z : (Fin n → Fin d) × (Fin m → Fin d) ↦
    (∏ t : Fin n, X (w (Fin.castAdd m t)) (z.1 t)) *
      (∏ t : Fin m, X (w (Fin.natAdd n t)) (z.2 t)) * (x z.1 * y z.2))
      (splitWordsEquiv n m v)) = _
  rw [(splitWordsEquiv (A := Fin d) n m).sum_comp (fun z ↦
    (∏ t : Fin n, X (w (Fin.castAdd m t)) (z.1 t)) *
      (∏ t : Fin m, X (w (Fin.natAdd n t)) (z.2 t)) * (x z.1 * y z.2)), Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro z hz
  ring

abbrev partitionTensorAction (mu : Fin d → ℕ) (hmu : Antitone mu)
    (X : Matrix (Fin d) (Fin d) ℂ) :=
  cyclicTensorOperator (partitionHighestTensor mu hmu) (fun i ↦ (mu i : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) X

def cartanProductAction (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor nu hnu)) →L[ℂ]
    tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor nu hnu)) :=
  ((tensorOperator ((∑ i, mu i) + ∑ i, nu i) X).comp
    (tensorProductSector (cyclicSector (partitionHighestTensor mu hmu))
      (cyclicSector (partitionHighestTensor nu hnu))).subtypeL).codRestrict _ (fun x ↦
    generatorInvariant_tensorOperator_invariant _
      (fun a b z hz ↦ tensorProductSector_generator_invariant _ _
        (fun a b y hy ↦ cyclicSector_generator_invariant _ (fun i ↦ (mu i : ℂ))
          (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) a b hy)
        (fun a b y hy ↦ cyclicSector_generator_invariant _ (fun i ↦ (nu i : ℂ))
          (partitionHighestTensor_cartan nu hnu) (partitionHighestTensor_raising_zero nu hnu) a b hy)
        a b hz) X x.property)

@[simp] theorem cartanProductAction_coe (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) (x : tensorProductSector
      (cyclicSector (partitionHighestTensor mu hmu)) (cyclicSector (partitionHighestTensor nu hnu))) :
    (cartanProductAction mu nu hmu hnu X x : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)) =
      tensorOperator ((∑ i, mu i) + ∑ i, nu i) X (x : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)) := rfl

theorem cartanProductAction_star (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    cartanProductAction mu nu hmu hnu Xᴴ = (cartanProductAction mu nu hmu hnu X).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change ⟪tensorOperator ((∑ i, mu i) + ∑ i, nu i) Xᴴ
      (x : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)),
      (y : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d))⟫_ℂ =
    ⟪(x : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)),
      tensorOperator ((∑ i, mu i) + ∑ i, nu i) X
        (y : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d))⟫_ℂ
  rw [tensorOperator_star, ContinuousLinearMap.adjoint_inner_left]

/-- Exact Cartan equivariance is derived from the actual highest-vector
isometry, including singular matrices. -/
theorem cartanInclusion_tensorAction (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (cartanInclusion mu nu hmu hnu).toContinuousLinearMap.comp
      (partitionTensorAction (fun i ↦ mu i + nu i) (sumPartition_antitone mu nu hmu hnu) X) =
    (cartanProductAction mu nu hmu hnu X).comp
      (cartanInclusion mu nu hmu hnu).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun z : cyclicSector (cartanHighest mu nu hmu hnu) ↦
    (z : TensorRegister ((∑ i, mu i) + ∑ i, nu i) (Fin d)))
    (highestCyclicIsometry_tensorOperator _ _ (fun i ↦ ((mu i + nu i : ℕ) : ℂ))
      (partitionHighestTensor_cartan _ _) (cartanHighest_cartan mu nu hmu hnu)
      (partitionHighestTensor_raising_zero _ _) (cartanHighest_raising_zero mu nu hmu hnu)
      (partitionHighestTensor_norm _ _) (cartanHighest_norm mu nu hmu hnu) X x)

end Cloning.TensorLie
