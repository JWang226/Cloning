import Cloning.GeneralSymmetricDimension
import Cloning.MultimodeCoherent
import Cloning.IsometricRecovery
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal normalized local pure states in any finite one-particle dimension,
their tensor powers, and occupation coordinates in the physical symmetric
subspace. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
namespace Cloning.GeneralCoherent
open GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def energy {s : ℕ} (z : Fin s → ℂ) : ℝ := ∑ i, ‖z i‖ ^ 2

theorem energy_nonneg {s : ℕ} (z : Fin s → ℂ) : 0 ≤ energy z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def oneParticle {s : ℕ} (z : Fin s → ℂ) (L : ℕ) : Fin (s + 1) → ℂ :=
  fun a => (Fin.cons (1 : ℂ) (fun i : Fin s => z i / (Real.sqrt (L : ℝ) : ℂ)) : Fin (s + 1) → ℂ) a /
    (Real.sqrt (1 + energy z / L) : ℂ)

@[simp] theorem oneParticle_zero {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    oneParticle z L 0 = 1 / (Real.sqrt (1 + energy z / L) : ℂ) := rfl
@[simp] theorem oneParticle_succ {s : ℕ} (z : Fin s → ℂ) (L : ℕ) (i : Fin s) :
    oneParticle z L i.succ = (z i / (Real.sqrt (L : ℝ) : ℂ)) /
      (Real.sqrt (1 + energy z / L) : ℂ) := rfl

theorem oneParticle_norm_sq_sum {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ∑ a, ‖oneParticle z L a‖ ^ 2 = 1 := by
  have he := energy_nonneg z
  have hden : 0 < 1 + energy z / L := by positivity
  simp only [oneParticle, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hden.le]
  rw [← Finset.sum_div, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, norm_one, one_pow, norm_div, div_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg L), ← Finset.sum_div]
  change (1 + energy z / L) / (1 + energy z / L) = 1
  exact div_self hden.ne'

/-- The actual normalized tensor power in the computational word basis. -/
def productTensor {s : ℕ} (z : Fin s → ℂ) (L : ℕ) : TensorSpace L (s + 1) :=
  ⟨fun w => ∏ i, oneParticle z L (w i),
    memℓp_gen (by simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem productTensor_apply {s : ℕ} (z : Fin s → ℂ) (L : ℕ)
    (w : Word L (s + 1)) : productTensor z L w = ∏ i, oneParticle z L (w i) := rfl

theorem productTensor_norm {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖productTensor z L‖ = 1 := by
  have hs : ‖productTensor z L‖ ^ (2 : ℕ) = 1 := by
    calc
      _ = ∑ w : Word L (s + 1), ‖∏ i, oneParticle z L (w i)‖ ^ (2 : ℕ) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype, productTensor_apply] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (productTensor z L)
      _ = ∑ w : Word L (s + 1), ∏ i, ‖oneParticle z L (w i)‖ ^ (2 : ℕ) := by
        simp only [norm_prod, Finset.prod_pow]
      _ = ∏ i : Fin L, ∑ a : Fin (s + 1), ‖oneParticle z L a‖ ^ (2 : ℕ) := by
        exact (Fintype.prod_sum (fun (_ : Fin L) (a : Fin (s + 1)) => ‖oneParticle z L a‖ ^ (2 : ℕ))).symm
      _ = 1 := by simp only [oneParticle_norm_sq_sum, Finset.prod_const_one]
  nlinarith [norm_nonneg (productTensor z L)]

theorem productTensor_symmetric {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    productTensor z L ∈ symmetricSubspace L (s + 1) := by
  intro w σ
  simp only [productTensor_apply, Function.comp_apply]
  exact Equiv.prod_comp σ (fun i => oneParticle z L (w i))

/-- Exact finite occupation coordinates of the normalized tensor power. -/
def finiteProductVector {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    OccupationSpace L (s + 1) :=
  (isometry L (s + 1)).toContinuousLinearMap.adjoint (productTensor z L)

theorem isometry_finiteProductVector {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    isometry L (s + 1) (finiteProductVector z L) = productTensor z L := by
  have hr : productTensor z L ∈ (isometry L (s + 1)).toLinearMap.range := by
    rw [isometry_range]
    exact productTensor_symmetric z L
  obtain ⟨v, hv⟩ := hr
  change isometry L (s + 1)
    ((isometry L (s + 1)).toContinuousLinearMap.adjoint (productTensor z L)) = _
  rw [← hv]
  change isometry L (s + 1) ((isometry L (s + 1)).toContinuousLinearMap.adjoint
    (isometry L (s + 1) v)) = isometry L (s + 1) v
  rw [InfiniteTraceClass.isometry_adjoint_apply_self]

theorem finiteProductVector_norm {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖finiteProductVector z L‖ = 1 := by
  rw [← (isometry L (s + 1)).norm_map, isometry_finiteProductVector, productTensor_norm]

end Cloning.GeneralCoherent
