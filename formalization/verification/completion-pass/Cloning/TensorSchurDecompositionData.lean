import Cloning.TensorHighestExtraction
import Cloning.TensorHighestGramCovariance

/-! Actual normalized physical highest tensors and their canonical sector identifications. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Actual tensor data. Every field is proved by highest extraction below. -/
structure PhysicalHighestTensor (n d : ℕ) where
  weight : Fin d → ℕ
  weight_antitone : Antitone weight
  weight_sum : (∑ a, weight a) = n
  vector : TensorRegister n (Fin d)
  norm_one : ‖vector‖ = 1
  cartan : ∀ a, collectiveGenerator n a a vector = (weight a : ℂ) • vector
  raising : ∀ a b, a < b → collectiveGenerator n a b vector = 0

namespace PhysicalHighestTensor

def sector (H : PhysicalHighestTensor n d) : Submodule ℂ (TensorRegister n (Fin d)) :=
  cyclicSector H.vector

theorem vector_mem (H : PhysicalHighestTensor n d) : H.vector ∈ H.sector :=
  highest_mem_cyclicSector H.vector

theorem sector_ne_bot (H : PhysicalHighestTensor n d) : H.sector ≠ ⊥ := by
  intro he
  have hz : H.vector = 0 := by simpa only [he, Submodule.mem_bot] using H.vector_mem
  have hn := H.norm_one
  simp only [hz, norm_zero, zero_ne_one] at hn

theorem generator_invariant (H : PhysicalHighestTensor n d) (a b : Fin d)
    {x : TensorRegister n (Fin d)} (hx : x ∈ H.sector) : collectiveGenerator n a b x ∈ H.sector :=
  cyclicSector_generator_invariant H.vector (fun i => (H.weight i : ℂ)) H.cartan H.raising a b hx

theorem tensorOperator_invariant (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ) {x : TensorRegister n (Fin d)} (hx : x ∈ H.sector) :
    tensorOperator n X x ∈ H.sector :=
  cyclicSector_tensorOperator_invariant H.vector (fun i => (H.weight i : ℂ)) H.cartan H.raising X hx

theorem irreducible (H : PhysicalHighestTensor n d)
    (W : Submodule ℂ (TensorRegister n (Fin d))) (hW : W ≤ H.sector)
    (hInv : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W) : W = ⊥ ∨ W = H.sector :=
  cyclicSector_irreducible H.vector H.norm_one H.raising W hW hInv

/-- The canonical partition copy is exactly isometric to this physical copy. -/
def canonicalIsometry (H : PhysicalHighestTensor n d) :
    cyclicSector (partitionHighestTensor H.weight H.weight_antitone) ≃ₗᵢ[ℂ] H.sector :=
  highestCyclicIsometry (partitionHighestTensor H.weight H.weight_antitone) H.vector
    (fun i => (H.weight i : ℂ)) (partitionHighestTensor_cartan H.weight H.weight_antitone)
    H.cartan (partitionHighestTensor_raising_zero H.weight H.weight_antitone) H.raising
    (partitionHighestTensor_norm H.weight H.weight_antitone) H.norm_one

theorem canonicalIsometry_tensorOperator (H : PhysicalHighestTensor n d)
    (X : Matrix (Fin d) (Fin d) ℂ)
    (x : cyclicSector (partitionHighestTensor H.weight H.weight_antitone)) :
    H.canonicalIsometry (cyclicTensorOperator
        (partitionHighestTensor H.weight H.weight_antitone) (fun i => (H.weight i : ℂ))
        (partitionHighestTensor_cartan H.weight H.weight_antitone)
        (partitionHighestTensor_raising_zero H.weight H.weight_antitone) X x) =
      cyclicTensorOperator H.vector (fun i => (H.weight i : ℂ)) H.cartan H.raising X
        (H.canonicalIsometry x) :=
  highestCyclicIsometry_tensorOperator (partitionHighestTensor H.weight H.weight_antitone) H.vector
    (fun i => (H.weight i : ℂ)) (partitionHighestTensor_cartan H.weight H.weight_antitone)
    H.cartan (partitionHighestTensor_raising_zero H.weight H.weight_antitone) H.raising
    (partitionHighestTensor_norm H.weight H.weight_antitone) H.norm_one X x

end PhysicalHighestTensor

/-- Invariance propagates membership of the highest vector to its entire cyclic sector. -/
theorem cyclicSector_le_of_mem_of_invariant
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (Ω : TensorRegister n (Fin d)) (hΩ : Ω ∈ W) : cyclicSector Ω ≤ W := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩
  induction w with
  | nil => exact hΩ
  | cons a w ih => exact hW a.val.2 a.val.1 _ ih

/-- Actual extraction produces a nonzero irreducible physical cyclic summand. -/
theorem exists_physicalHighestTensor_le
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W) (hWne : W ≠ ⊥) :
    ∃ H : PhysicalHighestTensor n d, H.sector ≤ W := by
  obtain ⟨mu, hmu, hsum, Ω, hΩW, hΩ, hweight, hraise⟩ :=
    exists_partitionHighest_in_invariant W hW hWne
  exact ⟨⟨mu, hmu, hsum, Ω, hΩ, hweight, hraise⟩,
    cyclicSector_le_of_mem_of_invariant W hW Ω hΩW⟩

/-- Adjoint closure makes the orthogonal complement invariant under all generators. -/
theorem generatorInvariant_orthogonal
    (W : Submodule ℂ (TensorRegister n (Fin d)))
    (hW : ∀ a b x, x ∈ W → collectiveGenerator n a b x ∈ W)
    (a b : Fin d) {x : TensorRegister n (Fin d)} (hx : x ∈ Wᗮ) :
    collectiveGenerator n a b x ∈ Wᗮ := by
  apply (W.mem_orthogonal _).mpr
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_left, collectiveGenerator_adjoint]
  exact W.inner_right_of_mem_orthogonal (hW b a y hy) hx

end Cloning.TensorLie
