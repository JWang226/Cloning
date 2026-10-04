import Cloning.TensorFlatProjectorPadding

/-! The actual ambient rank-flat Young law is exactly the padded smaller-rank law. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n r k : ℕ}

theorem rankFlatSpectrum_antitone (r k : ℕ) : Antitone (rankFlatSpectrum r k) := by
  intro a b hab
  unfold rankFlatSpectrum
  split_ifs with hb ha
  · exact le_rfl
  · have hv : a.val ≤ b.val := hab
    omega
  · positivity
  · exact le_rfl

theorem rankFlatSpectrum_sum (hr : 0 < r) : ∑ a, rankFlatSpectrum r k a = 1 := by
  rw [Fin.sum_univ_add]
  have hl (a : Fin r) : rankFlatSpectrum r k (Fin.castAdd k a) = 1/(r:ℝ) := by
    simp [rankFlatSpectrum, a.isLt]
  have ht (a : Fin k) : rankFlatSpectrum r k (Fin.natAdd r a) = 0 := by
    simp [rankFlatSpectrum, Fin.val_natAdd]
  simp only [hl, ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_const_zero, mul_zero, add_zero]
  simpa only [div_eq_mul_inv, one_mul] using div_self (Nat.cast_ne_zero.mpr hr.ne' : (r:ℝ)≠0)

def padShape (mu : Shape r n) (k : ℕ) : Shape (r+k) n :=
  Fin.append mu (fun _ => 0)

theorem padShape_val (mu : Shape r n) (k : ℕ) :
    (fun a => (padShape mu k a).val) = padPartition (fun a => (mu a).val) k := by
  funext a
  induction a using Fin.addCases <;> simp [padShape, padPartition]

theorem padShape_injective (k : ℕ) : Function.Injective (fun mu : Shape r n => padShape mu k) := by
  intro mu nu he
  funext a
  have hh := congrFun he (Fin.castAdd k a)
  simpa only [padShape, Fin.append_left] using hh

def tensorRankFlatYoungPMF (n r k : ℕ) (hr : 0 < r) : PMF (Shape (r+k) n) :=
  tensorYoungPMF n (r+k) (rankFlatSpectrum r k) (rankFlatSpectrum_nonneg r k) (rankFlatSpectrum_sum hr)

theorem physicalSectorCharacter_rankFlat_zero (mu : Fin (r+k) → ℕ)
    (a : Fin (r+k)) (ha : r ≤ a.val) (hmu : mu a ≠ 0) :
    physicalSectorCharacter mu (rankFlatSpectrum r k) = 0 := by
  have hb := physicalSectorCharacter_le_polynomial_highest mu (rankFlatSpectrum r k)
    (rankFlatSpectrum_nonneg r k) (rankFlatSpectrum_antitone r k)
  have hp : (∏ b, rankFlatSpectrum r k b ^ mu b) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [rankFlatSpectrum, not_lt.mpr ha, hmu]
  rw [hp, mul_zero] at hb
  exact le_antisymm hb (physicalSectorCharacter_nonneg _ _)

theorem physicalSectorCharacter_pad_rankFlat (mu : Fin r → ℕ) (k : ℕ) :
    physicalSectorCharacter (padPartition mu k) (rankFlatSpectrum r k) =
      physicalSectorCharacter mu (flatSpectrum r) := by
  classical
  by_cases hmu : Antitone mu
  · rw [physicalSectorCharacter_rankFlat mu hmu k]
    rw [physicalSectorCharacter, dif_pos hmu]
    change _ = sectorPartitionFunction _ _ _ _ (fun _ => 1/(r:ℝ))
    rw [sectorPartitionFunction_const _ _ _ _ _ (by positivity)]
    change _ = (1/(r:ℝ))^(∑a,mu a) * (partitionDimension mu hmu : ℝ)
    rw [one_div_pow]
    ring
  · have hpad : ¬ Antitone (padPartition mu k) := by
      intro h
      exact hmu (fun a b hab => by
        simpa only [padPartition_left] using h (show Fin.castAdd k a ≤ Fin.castAdd k b from hab))
    simp only [physicalSectorCharacter, dif_neg hmu, dif_neg hpad]

theorem tensorRankFlatYoungPMF_pad (hr : 0 < r) (mu : Shape r n) :
    tensorRankFlatYoungPMF n r k hr (padShape mu k) = tensorFlatYoungPMF n r hr mu := by
  apply (ENNReal.toReal_eq_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [tensorRankFlatYoungPMF, tensorFlatYoungPMF, tensorYoungPMF_formula, tensorYoungPMF_formula,
    padShape_val, standardCount_padPartition, physicalSectorCharacter_pad_rankFlat]

theorem tensorRankFlatYoungPMF_outside (hr : 0 < r) (mu : Shape (r+k) n)
    (hmu : mu ∉ Set.range (fun nu : Shape r n => padShape nu k)) :
    tensorRankFlatYoungPMF n r k hr mu = 0 := by
  classical
  have hex : ∃ a : Fin k, (mu (Fin.natAdd r a)).val ≠ 0 := by
    by_contra! hn
    apply hmu
    refine ⟨(fun a => mu (Fin.castAdd k a)), ?_⟩
    funext a
    induction a using Fin.addCases with
    | left a => simp [padShape]
    | right a =>
      apply Fin.ext
      simpa only [padShape, Fin.append_right, Fin.val_zero] using (hn a).symm
  obtain ⟨a,ha⟩ := hex
  have hc := physicalSectorCharacter_rankFlat_zero (fun a => (mu a).val)
    (Fin.natAdd r a) (by simp [Fin.val_natAdd]) ha
  apply (ENNReal.toReal_eq_toReal (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  rw [ENNReal.toReal_zero]
  rw [tensorRankFlatYoungPMF, tensorYoungPMF_formula, hc, mul_zero]

/-- Exact equality of the physical PMFs, including labels outside the support. -/
theorem tensorRankFlatYoungPMF_eq_map (hr : 0 < r) :
    tensorRankFlatYoungPMF n r k hr = (tensorFlatYoungPMF n r hr).map (fun mu => padShape mu k) := by
  classical
  apply PMF.ext
  intro mu
  rw [PMF.map_apply, tsum_fintype]
  by_cases hm : mu ∈ Set.range (fun nu : Shape r n => padShape nu k)
  · obtain ⟨nu,rfl⟩ := hm
    rw [tensorRankFlatYoungPMF_pad]
    simp only [(padShape_injective k).eq_iff]
    simp
  · rw [tensorRankFlatYoungPMF_outside hr mu hm]
    symm
    apply Finset.sum_eq_zero
    intro nu _
    exact if_neg (fun he => hm ⟨nu,he.symm⟩)

end Cloning.TensorLie
