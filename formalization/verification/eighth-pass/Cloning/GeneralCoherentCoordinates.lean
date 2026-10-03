import Cloning.GeneralCoherentModel
import Cloning.GeneralCoherentMultiplicity
import Cloning.WernerPhysicalPullback

/-! Exact coefficients of arbitrary-dimensional tensor powers in multimode
Fock space, derived from the physical occupation isometry. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
namespace Cloning.GeneralCoherent
open GeneralSymmetricOccupation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Group the literal tensor-product coefficients by their occupation counts. -/
theorem word_prod_eq_profile {L d : ℕ} (x : Fin d → ℂ) (w : Word L d) :
    (∏ i, x (w i)) = ∏ a, x a ^ profile w a := by
  simpa only [Finset.prod_const, Finset.card_univ, profile] using
    (Fintype.prod_fiberwise' w x).symm

theorem finiteProductVector_apply {s : ℕ} (z : Fin s → ℂ) (L : ℕ)
    (q : Occupation L (s + 1)) :
    finiteProductVector z L q = (Real.sqrt (multiplicity q : ℝ) : ℂ) *
      ∏ a, oneParticle z L a ^ q.val a := by
  obtain ⟨w, hw⟩ := label_surjective L (s + 1) q
  have h := congrArg (fun v : TensorSpace L (s + 1) => v w)
    (isometry_finiteProductVector z L)
  dsimp only at h
  rw [isometry_apply, hw, productTensor_apply, word_prod_eq_profile] at h
  have hp : profile w = q.val := congrArg Subtype.val hw
  rw [hp] at h
  have hm : (Real.sqrt (multiplicity q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos q)).ne'
  exact (div_eq_iff hm).mp h |>.trans (mul_comm _ _)

/-- Full multimode padded occupation vector of the physical normalized tensor. -/
def productVector {s : ℕ} (z : Fin s → ℂ) (L : ℕ) : FockSpace s :=
  occupationPad L s (finiteProductVector z L)

theorem productVector_norm {s : ℕ} (z : Fin s → ℂ) (L : ℕ) :
    ‖productVector z L‖ = 1 := by
  rw [productVector, LinearIsometry.norm_map, finiteProductVector_norm]

theorem occupationPad_apply_of_le {L s : ℕ} (v : OccupationSpace L (s + 1))
    (k : Fin s → ℕ) (hk : (∑ i, k i) ≤ L) :
    occupationPad L s v k = v (fromExcitation k hk) := by
  classical
  rw [occupationPad, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp only [LinearIsometry.toSpanSingleton_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, numberVector, lp.single_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (fromExcitation k hk)]
  · simp
  · intro q hq hne
    have hx : k ≠ excitation q := by
      intro h
      exact hne (excitation_injective L s (h.symm.trans (excitation_fromExcitation k hk).symm))
    simp [hx]
  · simp

theorem occupationPad_apply_of_lt {L s : ℕ} (v : OccupationSpace L (s + 1))
    (k : Fin s → ℕ) (hk : L < ∑ i, k i) : occupationPad L s v k = 0 := by
  classical
  rw [occupationPad, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp only [LinearIsometry.toSpanSingleton_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, numberVector, lp.single_apply, Pi.single_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro q hq
  have hx : k ≠ excitation q := by intro h; exact (not_le_of_gt hk) (h ▸ excitation_sum_le q)
  simp [hx]

theorem productVector_apply_of_le {s : ℕ} (z : Fin s → ℂ) (L : ℕ)
    (k : Fin s → ℕ) (hk : (∑ i, k i) ≤ L) :
    productVector z L k =
      (Real.sqrt (multiplicity (fromExcitation k hk) : ℝ) : ℂ) *
        ∏ a, oneParticle z L a ^ (fromExcitation k hk).val a := by
  rw [productVector, occupationPad_apply_of_le _ k hk, finiteProductVector_apply]

/-- The multinomial multiplicity with the vacuum occupation eliminated. -/
theorem multiplicity_fromExcitation_mul {L s : ℕ} (k : Fin s → ℕ)
    (hk : (∑ i, k i) ≤ L) :
    multiplicity (fromExcitation k hk) * ∏ i, (k i).factorial =
      L.choose (∑ i, k i) * (∑ i, k i).factorial := by
  have hm := multiplicity_mul_factorials (fromExcitation k hk)
  simp only [fromExcitation, GeneralSymmetricOccupation.compositionEquiv, Fin.prod_univ_succ] at hm
  have hc := Nat.choose_mul_factorial_mul_factorial hk
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (L - ∑ i, k i))
  calc
    _ = multiplicity (fromExcitation k hk) *
      ((L - ∑ i, k i).factorial * ∏ i, (k i).factorial) := by ring
    _ = L.factorial := hm
    _ = _ := by rw [← hc]; ring

/-- All amplitude dependence in an occupation coefficient is explicit. -/
theorem oneParticle_occupation_product {s : ℕ} (z : Fin s → ℂ) (L : ℕ)
    (q : Occupation L (s + 1)) :
    (∏ a, oneParticle z L a ^ q.val a) =
      (∏ i, z i ^ excitation q i) /
        (Real.sqrt (L : ℝ) : ℂ) ^ (∑ i, excitation q i) /
        (Real.sqrt (1 + energy z / L) : ℂ) ^ L := by
  simp only [oneParticle, div_pow, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, occupation_sum]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, one_pow, one_mul, Fin.cons_succ, div_pow,
    Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, excitation]

end Cloning.GeneralCoherent
