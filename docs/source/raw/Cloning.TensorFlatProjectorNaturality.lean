import Cloning.TensorFlatProjectorEmbedding
import Cloning.TensorFlatProjectorDimensions

/-! Exact Lie naturality and padded highest tensors under coordinate inclusion. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r k : ℕ}

theorem coordinateWordEmbedding_update (v : Fin n → Fin r) (t : Fin n) (a : Fin r) :
    coordinateWordEmbedding n r k (Function.update v t a) =
      Function.update (coordinateWordEmbedding n r k v) t (Fin.castAdd k a) := by
  funext s
  by_cases h : s = t
  · subst s; simp [coordinateWordEmbedding]
  · simp [coordinateWordEmbedding, Function.update_of_ne h]

/-- Coordinate tensor inclusion intertwines every supported matrix unit. -/
theorem coordinateTensorEmbedding_slot (x : TensorRegister n (Fin r)) (t : Fin n)
    (a b : Fin r) :
    coordinateTensorEmbedding n r k (slotGenerator t a b x) =
      slotGenerator t (Fin.castAdd k a) (Fin.castAdd k b) (coordinateTensorEmbedding n r k x) := by
  let I := coordinateTensorEmbedding n r k
  have he : I.toLinearMap.comp (slotGenerator t a b).toLinearMap =
      (slotGenerator t (Fin.castAdd k a) (Fin.castAdd k b)).toLinearMap.comp I.toLinearMap := by
    apply (registerBasis (Fin n → Fin r)).toOrthonormalBasis.toBasis.ext
    intro v
    simp only [OrthonormalBasis.coe_toBasis, HilbertBasis.coe_toOrthonormalBasis]
    change I (slotGenerator t a b (registerBasis _ v)) =
      slotGenerator t (Fin.castAdd k a) (Fin.castAdd k b) (I (registerBasis _ v))
    dsimp only [I]
    rw [coordinateTensorEmbedding_basis, slotGenerator_basis, slotGenerator_basis]
    by_cases hv : v t = b
    · simp only [hv, if_true, Fin.castAdd_inj, coordinateTensorEmbedding_basis]
      congr 1
      exact coordinateWordEmbedding_update v t a
    · simp only [hv, if_false, Fin.castAdd_inj, map_zero]
  exact LinearMap.congr_fun he x

theorem coordinateTensorEmbedding_collective (x : TensorRegister n (Fin r)) (a b : Fin r) :
    coordinateTensorEmbedding n r k (collectiveGenerator n a b x) =
      collectiveGenerator n (Fin.castAdd k a) (Fin.castAdd k b) (coordinateTensorEmbedding n r k x) := by
  simp only [collectiveGenerator, ContinuousLinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun t _ => coordinateTensorEmbedding_slot x t a b)

/-- An unsupported input column of a matrix unit kills every embedded tensor. -/
theorem coordinateTensorEmbedding_slot_outside (x : TensorRegister n (Fin r)) (t : Fin n)
    (a : Fin (r+k)) (b : Fin k) :
    slotGenerator t a (Fin.natAdd r b) (coordinateTensorEmbedding n r k x) = 0 := by
  let I := coordinateTensorEmbedding n r k
  have he : (slotGenerator t a (Fin.natAdd r b)).toLinearMap.comp I.toLinearMap = 0 := by
    apply (registerBasis (Fin n → Fin r)).toOrthonormalBasis.toBasis.ext
    intro v
    simp only [OrthonormalBasis.coe_toBasis, HilbertBasis.coe_toOrthonormalBasis]
    change slotGenerator t a (Fin.natAdd r b) (I (registerBasis _ v)) = 0
    dsimp only [I]
    rw [coordinateTensorEmbedding_basis, slotGenerator_basis]
    have hne : Fin.castAdd k (v t) ≠ Fin.natAdd r b := by
      intro h
      have hv := (v t).isLt
      have hh := congrArg Fin.val h
      change (v t).val = r+b.val at hh
      omega
    simp [hne]
  exact LinearMap.congr_fun he x

theorem coordinateTensorEmbedding_collective_outside (x : TensorRegister n (Fin r))
    (a : Fin (r+k)) (b : Fin k) :
    collectiveGenerator n a (Fin.natAdd r b) (coordinateTensorEmbedding n r k x) = 0 := by
  simp only [collectiveGenerator, ContinuousLinearMap.sum_apply,
    coordinateTensorEmbedding_slot_outside, Finset.sum_const_zero]

/-- Every actual highest tensor embeds as a highest tensor of the padded weight. -/
theorem coordinateTensorEmbedding_highest
    (Ω : TensorRegister n (Fin r)) (mu : Fin r → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0) :
    (∀ a, collectiveGenerator n a a (coordinateTensorEmbedding n r k Ω) =
      (padPartition mu k a : ℂ) • coordinateTensorEmbedding n r k Ω) ∧
    (∀ a b, a < b → collectiveGenerator n a b (coordinateTensorEmbedding n r k Ω) = 0) := by
  constructor
  · intro a
    induction a using Fin.addCases with
    | left a => rw [← coordinateTensorEmbedding_collective, hweight, map_smul, padPartition_left]
    | right a => simp [coordinateTensorEmbedding_collective_outside]
  · intro a b
    induction b using Fin.addCases with
    | right b => intro _; exact coordinateTensorEmbedding_collective_outside Ω a b
    | left b =>
      induction a using Fin.addCases with
      | left a =>
        intro hab
        rw [← coordinateTensorEmbedding_collective, hraise a b (show a < b from hab), map_zero]
      | right a =>
        intro hab
        have hh : r+a.val < b.val := hab
        omega

end Cloning.TensorLie
