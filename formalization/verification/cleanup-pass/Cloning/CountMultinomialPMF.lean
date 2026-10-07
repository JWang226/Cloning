import Cloning.GeneralCoherentMultiplicity
import Cloning.YoungUniformLocalPhysicalLattice
import Cloning.YoungMultinomialLocalStirling

/-! The actual independent-word count PMF and its exact factorial multinomial mass. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter MeasureTheory
namespace Cloning.CountMultinomial
open Cloning.YoungGeneral Cloning.GeneralSymmetricOccupation Cloning.YoungHyperplane Cloning.YoungMultinomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def wordPMF (d N : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    PMF (Word N d) :=
  PMF.ofFintype (fun w ↦ ENNReal.ofReal (wordWeight p w)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ ↦ wordWeight_nonneg p hp w),
      wordWeight_sum p hs, ENNReal.ofReal_one])

theorem wordPMF_toReal (d N : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (w : Word N d) : (wordPMF d N p hp hs w).toReal=wordWeight p w := by
  simp only [wordPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (wordWeight_nonneg p hp w)]

def countShape {d N : ℕ} (w : Word N d) : Shape d N := fun i ↦
  ⟨profile w i, Nat.lt_succ_of_le (by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) ↦ Nat.zero_le (profile w j))
      (Finset.mem_univ i)
    simpa only [profile_sum] using hh)⟩

theorem countShape_sum {d N : ℕ} (w : Word N d) : ∑ i, (countShape w i).val=N :=
  profile_sum w

theorem profile_eq_rowCount {d N : ℕ} (w : Word N d) (i : Fin d) : profile w i=rowCount w i := by
  simp only [profile, rowCount, Fintype.card_subtype]

theorem countShape_eq_iff {d N : ℕ} (w : Word N d) (μ : Shape d N) :
    countShape w=μ ↔ profile w=(fun i ↦ (μ i).val) := by
  constructor
  · intro h; exact congrArg (fun z : Shape d N ↦ fun i ↦ (z i).val) h
  · intro h; funext i; exact Fin.ext (congrFun h i)

def countPMF (d N : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    PMF (Shape d N) := (wordPMF d N p hp hs).map countShape

theorem countPMF_eq_sum (d N : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (μ : Shape d N) :
    (countPMF d N p hp hs μ).toReal=
      ∑ w : Word N d, if countShape w=μ then wordWeight p w else 0 := by
  rw [countPMF, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro w _
    by_cases hw : countShape w=μ
    · simp only [hw, if_pos, wordPMF_toReal]
    · simp only [Ne.symm hw, hw, if_false, ENNReal.toReal_zero]
  · intro w _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top

theorem countPMF_eq_zero_of_sum {d N : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (μ : Shape d N) (hμ : (∑ i, (μ i).val)≠N) :
    countPMF d N p hp hs μ=0 := by
  rw [countPMF, PMF.map_apply, tsum_fintype]
  apply Finset.sum_eq_zero
  intro w _
  have hw : μ≠countShape w := by intro h; exact hμ (h ▸ countShape_sum w)
  simp only [hw, if_false]

/-- This is the actual count law of independent letters, including its literal factorial weight. -/
theorem countPMF_formula (d N : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (μ : Shape d N) (hμ : ∑ i, (μ i).val=N) :
    (countPMF d N p hp hs μ).toReal=multinomialMass N p (fun i ↦ (μ i).val) := by
  let q : Occupation N d := ⟨fun i ↦ (μ i).val, exists_word_of_sum _ hμ⟩
  have he w : countShape w=μ ↔ label w=q := by
    rw [countShape_eq_iff]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  have hweight w (hw : countShape w=μ) : wordWeight p w=∏ i, p i^(μ i).val := by
    rw [wordWeight_eq_row_product]
    apply Finset.prod_congr rfl
    intro i _
    rw [← profile_eq_rowCount, congrFun ((countShape_eq_iff w μ).mp hw) i]
  rw [countPMF_eq_sum]
  have hsum : (∑ w : Word N d, if countShape w=μ then wordWeight p w else 0)=
      (multiplicity q : ℝ)*(∏ i, p i^(μ i).val) := by
    calc
      _ = ∑ w : Word N d, if label w=q then (∏ i, p i^(μ i).val) else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : countShape w=μ
        · simp only [hw, (he w).mp hw, if_pos, hweight w hw]
        · simp only [hw, (he w).not.mp hw, if_false]
      _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, GeneralSymmetricOccupation.multiplicity]
  rw [hsum]
  have hm := multiplicity_mul_factorials q
  have hmr : (multiplicity q : ℝ)*(∏ i, ((μ i).val.factorial : ℝ))=(N.factorial : ℝ) := by
    exact_mod_cast hm
  have hf : (∏ i, ((μ i).val.factorial : ℝ))≠0 := by positivity
  unfold multinomialMass
  apply (eq_div_iff hf).mpr
  rw [mul_assoc, mul_comm (∏ i, p i^(μ i).val), ← mul_assoc, hmr]

end Cloning.CountMultinomial
