import Cloning.TensorSchurHaarIntertwiner

/-! Exact Haar orthogonality of the matrix coefficients of actual physical
Schur sectors. Equal labels give the dimension-normalized Kronecker factors;
unequal highest weights give zero, including different tensor degrees. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix Topology Matrix.Norms.L2Operator
open MeasureTheory
namespace Cloning.TensorLie
open Cloning.PhysicalFlatConverse Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem partitionActionMatrix_unitary_intertwiner_eq_zero
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (hne : mu ≠ nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex nu hnu) ℂ)
    (hcomm : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      M * partitionActionMatrix nu hnu U = partitionActionMatrix mu hmu U * M) : M=0 := by
  let B := (partitionBasis mu hmu).toBasis
  let C := (partitionBasis nu hnu).toBasis
  let T := (Matrix.toLin C B M).toContinuousLinearMap
  have hT : ∀ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      T.comp (partitionTensorAction nu hnu U) = (partitionTensorAction mu hmu U).comp T := by
    intro U
    apply ContinuousLinearMap.coe_injective
    apply (LinearMap.toMatrix C B).injective
    rw [ContinuousLinearMap.coe_comp,ContinuousLinearMap.coe_comp,
      LinearMap.toMatrix_comp C C B,LinearMap.toMatrix_comp C B B]
    simpa only [T,LinearMap.coe_toContinuousLinearMap,LinearMap.toMatrix_toLin] using hcomm U
  have hn : (fun a => (mu a : ℂ)) ≠ (fun a => (nu a : ℂ)) := by
    intro hh
    apply hne
    funext a
    exact Nat.cast_injective (congrFun hh a)
  have ht := cyclicTensorOperator_unitary_intertwiner_eq_zero
    (partitionHighestTensor mu hmu) (partitionHighestTensor nu hnu)
    (fun a => (mu a : ℂ)) (fun a => (nu a : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_cartan nu hnu)
    (partitionHighestTensor_raising_zero mu hmu) (partitionHighestTensor_raising_zero nu hnu)
    hn (partitionHighestTensor_norm mu hmu) (partitionHighestTensor_norm nu hnu) T hT
  have hh := congrArg (fun F => LinearMap.toMatrix C B (F : _ →L[ℂ] _).toLinearMap) ht
  simpa only [T,LinearMap.coe_toContinuousLinearMap,LinearMap.toMatrix_toLin,
    ContinuousLinearMap.coe_zero,map_zero] using hh

def rectangularSandwichCLM {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) : Matrix I J ℂ →L[ℂ] Matrix I J ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun M := A*M*Bᴴ
    map_add' M N := by simp only [Matrix.mul_add,Matrix.add_mul]
    map_smul' c M := by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }

def matrixEntryCLM {I J : Type*} [Fintype I] [Fintype J] (i : I) (j : J) :
    Matrix I J ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun M := M i j
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

variable [Nonempty (Fin d)]

def mixedTwirl (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex nu hnu) ℂ) :=
  ∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    partitionActionMatrix mu hmu U * M * (partitionActionMatrix nu hnu U)ᴴ ∂unitaryHaar

theorem continuous_mixedSandwich (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex nu hnu) ℂ) :
    Continuous (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U * M * (partitionActionMatrix nu hnu U)ᴴ) := by
  have hμ : Continuous (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) => partitionActionMatrix mu hmu U) :=
    (continuous_partitionActionMatrix mu hmu).comp continuous_subtype_val
  have hν : Continuous (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) => partitionActionMatrix nu hnu U) :=
    (continuous_partitionActionMatrix nu hnu).comp continuous_subtype_val
  exact (hμ.matrix_mul continuous_const).matrix_mul hν.matrix_conjTranspose

theorem integrable_mixedSandwich (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex nu hnu) ℂ) :
    Integrable (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U * M * (partitionActionMatrix nu hnu U)ᴴ) unitaryHaar :=
  (continuous_mixedSandwich mu nu hmu hnu M).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem mixedTwirl_invariant (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (M : Matrix (PartitionIndex mu hmu) (PartitionIndex nu hnu) ℂ)
    (V : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    partitionActionMatrix mu hmu V * mixedTwirl mu nu hmu hnu M *
      (partitionActionMatrix nu hnu V)ᴴ = mixedTwirl mu nu hmu hnu M := by
  have hh := (rectangularSandwichCLM (partitionActionMatrix mu hmu V)
      (partitionActionMatrix nu hnu V)).integral_comp_comm (integrable_mixedSandwich mu nu hmu hnu M)
  change (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    partitionActionMatrix mu hmu V * (partitionActionMatrix mu hmu U * M *
      (partitionActionMatrix nu hnu U)ᴴ) * (partitionActionMatrix nu hnu V)ᴴ ∂unitaryHaar) =
    partitionActionMatrix mu hmu V * mixedTwirl mu nu hmu hnu M *
      (partitionActionMatrix nu hnu V)ᴴ at hh
  rw [← hh]
  have he (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
      partitionActionMatrix mu hmu V * (partitionActionMatrix mu hmu U * M *
        (partitionActionMatrix nu hnu U)ᴴ) * (partitionActionMatrix nu hnu V)ᴴ =
      partitionActionMatrix mu hmu (V*U) * M * (partitionActionMatrix nu hnu (V*U))ᴴ := by
    simp only [Submonoid.coe_mul,partitionActionMatrix_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  simp_rw [he]
  exact integral_mul_left_eq_self (μ := unitaryHaar)
    (fun U : unitary (Matrix (Fin d) (Fin d) ℂ) =>
      partitionActionMatrix mu hmu U*M*(partitionActionMatrix nu hnu U)ᴴ) V

theorem mixedTwirl_eq_zero (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hne : mu ≠ nu) (M : Matrix (PartitionIndex mu hmu) (PartitionIndex nu hnu) ℂ) :
    mixedTwirl mu nu hmu hnu M = 0 := by
  apply partitionActionMatrix_unitary_intertwiner_eq_zero mu nu hmu hnu hne
  intro U
  have hh := congrArg (fun X => X*partitionActionMatrix nu hnu U)
    (mixedTwirl_invariant mu nu hmu hnu M U)
  simpa only [Matrix.mul_assoc,partitionActionMatrix_unitary,Matrix.mul_one] using hh.symm

theorem matrixEntry_sandwich_single {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (i j : I) (k l : J) :
    (A*Matrix.single j l (1:ℂ)*Bᴴ) i k = A i j * star (B k l) := by
  rw [Matrix.mul_apply,Finset.sum_eq_single l]
  · simp only [Matrix.mul_single_apply_same,mul_one,Matrix.conjTranspose_apply]
  · intro b _ hbl
    rw [Matrix.mul_single_apply_of_ne (1:ℂ) j l i b hbl A,zero_mul]
  · simp

theorem integral_partition_coefficients_ne (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hne : mu ≠ nu)
    (i j : PartitionIndex mu hmu) (k l : PartitionIndex nu hnu) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      partitionActionMatrix mu hmu U i j * star (partitionActionMatrix nu hnu U k l) ∂unitaryHaar) = 0 := by
  have hh := (matrixEntryCLM i k).integral_comp_comm
    (integrable_mixedSandwich mu nu hmu hnu (Matrix.single j l (1:ℂ)))
  change (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    (partitionActionMatrix mu hmu U * Matrix.single j l (1:ℂ) * (partitionActionMatrix nu hnu U)ᴴ) i k ∂unitaryHaar) =
      mixedTwirl mu nu hmu hnu (Matrix.single j l (1:ℂ)) i k at hh
  simpa only [matrixEntry_sandwich_single,mixedTwirl_eq_zero mu nu hmu hnu hne,Matrix.zero_apply] using hh

theorem integral_partition_coefficients_same (mu : Fin d → ℕ) (hmu : Antitone mu)
    (i j k l : PartitionIndex mu hmu) :
    (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
      partitionActionMatrix mu hmu U i j * star (partitionActionMatrix mu hmu U k l) ∂unitaryHaar) =
        if i=k ∧ j=l then (partitionDimension mu hmu : ℂ)⁻¹ else 0 := by
  have hh := (matrixEntryCLM i k).integral_comp_comm
    (integrable_partitionSandwich mu hmu (Matrix.single j l (1:ℂ)))
  change (∫ U : unitary (Matrix (Fin d) (Fin d) ℂ),
    (partitionActionMatrix mu hmu U * Matrix.single j l (1:ℂ) * (partitionActionMatrix mu hmu U)ᴴ) i k ∂unitaryHaar) =
      partitionTwirl mu hmu (Matrix.single j l (1:ℂ)) i k at hh
  rw [partitionTwirl_eq] at hh
  simp only [matrixEntry_sandwich_single] at hh
  rw [hh]
  by_cases hik : i=k <;> by_cases hjl : j=l
  · subst k; subst l
    simp [Matrix.trace_single_eq_same]
  · simp [hik,hjl,Matrix.trace_single_eq_of_ne j l (1:ℂ) hjl]
  · simp [hik,hjl]
  · simp [hik,hjl]

end Cloning.TensorLie
