import Cloning.TensorLocalUnitaryTaylor
import Cloning.TensorCyclicPBW

/-! The actual normalized collective displacement generator: skew-adjointness,
physical cyclic-cutoff propagation, and a local norm bound uniform once the
highest-weight gaps exceed the fixed cutoff. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open NormedSpace Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n d : ℕ}

def rootGenerator (mu : Fin d → ℕ) (z : PositiveRoot d → ℂ) :
    TensorRegister n (Fin d) →L[ℂ] TensorRegister n (Fin d) :=
  ∑ a, (z a • normalizedCreator n mu a.val.1 a.val.2 -
    star (z a) • normalizedAnnihilator n mu a.val.1 a.val.2)

theorem normalizedAnnihilator_adjoint (mu : Fin d → ℕ) (a b : Fin d) :
    (normalizedAnnihilator n mu a b).adjoint = normalizedCreator n mu a b := by
  rw [← normalizedCreator_adjoint mu a b, ContinuousLinearMap.adjoint_adjoint]

theorem rootGenerator_skew (mu : Fin d → ℕ) (z : PositiveRoot d → ℂ) :
    (rootGenerator (n := n) mu z).adjoint = -(rootGenerator (n := n) mu z) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  simp only [rootGenerator, star_sum, star_sub, star_smul,
    ContinuousLinearMap.star_eq_adjoint, normalizedCreator_adjoint,
    normalizedAnnihilator_adjoint, star_star]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  abel

variable (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)

include hweight hraise

theorem annihilator_mem_cutoff (a : PositiveRoot d) (r : ℕ)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) :
    normalizedAnnihilator n mu a.val.1 a.val.2 x ∈ cyclicCutoff Ω r :=
  PBW.annihilator_mem_same_cutoff _ (fun r => cyclicCutoff Ω (r : ℤ))
    (cyclicCutoff_nat_monotone Ω)
    (fun y hy => normalizedAnnihilator_zero_cyclicCutoff Ω mu hweight hraise
      a.val.1 a.val.2 a.property hy)
    (fun r y hy => normalizedAnnihilator_lowers_cyclicCutoff Ω mu hweight hraise
      a.val.1 a.val.2 a.property r hy) r x hx

theorem rootGenerator_mem_cutoff (z : PositiveRoot d → ℂ) (r : ℕ)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω r) :
    rootGenerator (n := n) mu z x ∈ cyclicCutoff Ω ((r+d : ℕ) : ℤ) := by
  simp only [rootGenerator, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sub_mem
  · exact (cyclicCutoff Ω _).smul_mem _ (normalizedCreator_raises_cyclicCutoff Ω mu a r hx)
  · exact (cyclicCutoff Ω _).smul_mem _
      (cyclicCutoff_nat_monotone Ω (Nat.le_add_right r d)
        (annihilator_mem_cutoff Ω mu hweight hraise a r hx))

theorem normalizedCreator_cutoff_bound (a : PositiveRoot d) (R : ℕ)
    (hgap : 2 * ((R : ℝ)+1) ≤ (mu a.val.1 : ℝ) - mu a.val.2)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω R) :
    ‖normalizedCreator n mu a.val.1 a.val.2 x‖ ≤ Real.sqrt (((R : ℝ)+1)*2) * ‖x‖ := by
  have hg : 0 < (mu a.val.1 : ℝ) - mu a.val.2 := by have := Nat.cast_nonneg (α := ℝ) R; linarith
  have hb := PBW.creator_norm_le_cutoff
    (normalizedCreator n mu a.val.1 a.val.2) (normalizedAnnihilator n mu a.val.1 a.val.2)
    (fun r => cyclicCutoff Ω (r : ℤ)) (normalized_inner_adjoint mu a.val.1 a.val.2)
    (fun y hy => normalizedAnnihilator_zero_cyclicCutoff Ω mu hweight hraise
      a.val.1 a.val.2 a.property hy)
    (fun r y hy => normalizedAnnihilator_lowers_cyclicCutoff Ω mu hweight hraise
      a.val.1 a.val.2 a.property r hy) R 1 (by norm_num) ?_ R le_rfl x hx
  · simpa only [show (1 : ℝ)+1=2 by norm_num] using hb
  · intro r hr y hy
    apply (normalized_diagonal_defect_norm_le Ω mu hweight r hy a.val.1 a.val.2 hg).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
    apply (div_le_one hg).mpr
    have hr' : (r : ℝ) ≤ R := Nat.cast_le.mpr hr
    linarith

theorem normalizedAnnihilator_cutoff_bound (a : PositiveRoot d) (R : ℕ)
    (hgap : 2 * ((R : ℝ)+1) ≤ (mu a.val.1 : ℝ) - mu a.val.2)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω R) :
    ‖normalizedAnnihilator n mu a.val.1 a.val.2 x‖ ≤ Real.sqrt (((R : ℝ)+1)*2) * ‖x‖ :=
  PBW.annihilator_norm_le_from_local_creator _ _ (cyclicCutoff Ω R) _ (Real.sqrt_nonneg _)
    (normalized_inner_adjoint mu a.val.1 a.val.2)
    (fun y hy => normalizedCreator_cutoff_bound Ω mu hweight hraise a R hgap hy)
    x (annihilator_mem_cutoff Ω mu hweight hraise a R hx)

theorem rootGenerator_norm_le (z : PositiveRoot d → ℂ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 2 * ((R : ℝ)+1) ≤ (mu a.val.1 : ℝ) - mu a.val.2)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω R) :
    ‖rootGenerator (n := n) mu z x‖ ≤
      (2 * ∑ a, ‖z a‖) * Real.sqrt (((R : ℝ)+1)*2) * ‖x‖ := by
  simp only [rootGenerator, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  calc
    _ ≤ ∑ a : PositiveRoot d, ‖z a • normalizedCreator n mu a.val.1 a.val.2 x -
        star (z a) • normalizedAnnihilator n mu a.val.1 a.val.2 x‖ := norm_sum_le _ _
    _ ≤ ∑ a : PositiveRoot d, (‖z a‖ + ‖z a‖) *
        (Real.sqrt (((R : ℝ)+1)*2) * ‖x‖) := by
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sub_le _ _).trans
      rw [norm_smul, norm_smul, norm_star, add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (normalizedCreator_cutoff_bound Ω mu hweight hraise a R (hgap a) hx)
          (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (normalizedAnnihilator_cutoff_bound Ω mu hweight hraise a R (hgap a) hx)
          (norm_nonneg _))
    _ = (2 * ∑ a, ‖z a‖) * Real.sqrt (((R : ℝ)+1)*2) * ‖x‖ := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      ring

theorem rootGenerator_pow_mem (z : PositiveRoot d → ℂ) (R m : ℕ)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω R) :
    (rootGenerator (n := n) mu z ^ m) x ∈ cyclicCutoff Ω ((R+m*d : ℕ) : ℤ) := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    simpa only [Nat.succ_mul, Nat.add_assoc] using
      rootGenerator_mem_cutoff Ω mu hweight hraise z (R+m*d) ih

theorem rootGenerator_pow_norm_le (z : PositiveRoot d → ℂ) (R M : ℕ)
    (hgap : ∀ a : PositiveRoot d, 2 * (((R+M*d : ℕ) : ℝ)+1) ≤ (mu a.val.1 : ℝ) - mu a.val.2)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω R) :
    ‖(rootGenerator (n := n) mu z ^ M) x‖ ≤
      ((2 * ∑ a, ‖z a‖) * Real.sqrt ((((R+M*d : ℕ) : ℝ)+1)*2)) ^ M * ‖x‖ := by
  let C := (2 * ∑ a, ‖z a‖) * Real.sqrt ((((R+M*d : ℕ) : ℝ)+1)*2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpow : ∀ m ≤ M, ‖(rootGenerator (n := n) mu z ^ m) x‖ ≤ C ^ m * ‖x‖ := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hmem := rootGenerator_pow_mem Ω mu hweight hraise z R m hx
      have hmem' : (rootGenerator (n := n) mu z ^ m) x ∈ cyclicCutoff Ω ((R+M*d : ℕ) : ℤ) :=
        cyclicCutoff_nat_monotone Ω (Nat.add_le_add_left (Nat.mul_le_mul_right d (by omega : m ≤ M)) R) hmem
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      calc
        _ ≤ C * ‖(rootGenerator (n := n) mu z ^ m) x‖ := rootGenerator_norm_le Ω mu hweight hraise z _ hgap hmem'
        _ ≤ C * (C ^ m * ‖x‖) := mul_le_mul_of_nonneg_left (ih (by omega)) hC
        _ = C ^ (m+1) * ‖x‖ := by rw [pow_succ']; ring
  exact hpow M le_rfl

/-- The actual physical displacement exponential has a vector Taylor remainder
controlled by a fixed-cutoff constant, uniformly in all sufficiently large gaps. -/
theorem exp_rootGenerator_taylor_remainder (z : PositiveRoot d → ℂ) (R m : ℕ)
    (hgap : ∀ a : PositiveRoot d,
      2 * (((R+(m+1)*d : ℕ) : ℝ)+1) ≤ (mu a.val.1 : ℝ) - mu a.val.2)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicCutoff Ω R) :
    ‖exp (rootGenerator (n := n) mu z) x -
        ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) •
          ((rootGenerator (n := n) mu z ^ j) x)‖ ≤
      (((2 * ∑ a, ‖z a‖) * Real.sqrt ((((R+(m+1)*d : ℕ) : ℝ)+1)*2)) ^ (m+1) * ‖x‖) /
        m.factorial := by
  apply (exp_taylor_vector_remainder _ (rootGenerator_skew mu z) x m).trans
  exact div_le_div_of_nonneg_right
    (rootGenerator_pow_norm_le Ω mu hweight hraise z R (m+1) hgap hx)
    (Nat.cast_nonneg _)

end Cloning.TensorLocalUnitary
