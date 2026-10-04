import Cloning.YoungCompatibilityPMF
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Exact finite marginal completion of a common subcoupling. The residual is
an independent product with its forced normalization, including zero defect. -/
noncomputable section
open scoped BigOperators ENNReal
namespace Cloning.YoungFlatCoupling
open Finset
set_option maxHeartbeats 600000
variable {I J : Type*} [Fintype I] [Fintype J]

def commonMass (c : I → J → ℝ) : ℝ := ∑ i, ∑ j, c i j

def rowResidual (p : I → ℝ) (c : I → J → ℝ) (i : I) : ℝ := p i - ∑ j, c i j

def colResidual (q : J → ℝ) (c : I → J → ℝ) (j : J) : ℝ := q j - ∑ i, c i j

def completionWeight (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ) (i : I) (j : J) : ℝ :=
  c i j + rowResidual p c i * colResidual q c j / (1-commonMass c)

theorem rowResidual_sum (p : I → ℝ) (c : I → J → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, rowResidual p c i = 1-commonMass c := by
  simp only [rowResidual, Finset.sum_sub_distrib, hp, commonMass]

theorem colResidual_sum (q : J → ℝ) (c : I → J → ℝ) (hq : ∑ j, q j = 1) :
    ∑ j, colResidual q c j = 1-commonMass c := by
  simp only [colResidual, Finset.sum_sub_distrib, hq, commonMass]
  rw [Finset.sum_comm]

theorem commonMass_le_one (p : I → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hr : ∀ i, ∑ j, c i j ≤ p i) : commonMass c ≤ 1 := by
  exact (Finset.sum_le_sum (fun i _ => hr i)).trans_eq hp

theorem completionWeight_nonneg (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hc : ∀ i j, 0 ≤ c i j)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j) (i : I) (j : J) :
    0 ≤ completionWeight p q c i j :=
  add_nonneg (hc i j) (div_nonneg (mul_nonneg (sub_nonneg.mpr (hr i)) (sub_nonneg.mpr (hs j)))
    (sub_nonneg.mpr (commonMass_le_one p c hp hr)))

theorem completionWeight_row (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (i : I) :
    ∑ j, completionWeight p q c i j = p i := by
  classical
  have hsum := rowResidual_sum p c hp
  have hres : 0 ≤ rowResidual p c i := sub_nonneg.mpr (hr i)
  have hle : rowResidual p c i ≤ 1-commonMass c := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hr j)) (Finset.mem_univ i)
  simp only [completionWeight, Finset.sum_add_distrib, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum, colResidual_sum q c hq]
  by_cases ha : 1-commonMass c = 0
  · have hz : rowResidual p c i = 0 := le_antisymm (hle.trans_eq ha) hres
    have he : ∑ j, c i j = p i := by dsimp only [rowResidual] at hz; linarith
    rw [hz, zero_mul, zero_mul, add_zero, he]
  · rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    simp only [rowResidual]
    ring

theorem completionWeight_col (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1)
    (hs : ∀ j, ∑ i, c i j ≤ q j) (j : J) :
    ∑ i, completionWeight p q c i j = q j := by
  classical
  have he : completionWeight p q c = fun i j => completionWeight q p (fun j i => c i j) j i := by
    funext i j
    unfold completionWeight rowResidual colResidual commonMass
    rw [Finset.sum_comm (f := fun i j => c i j)]
    ring
  rw [he]
  exact completionWeight_row q p (fun j i => c i j) hq hp hs j

theorem completionWeight_sum (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (hr : ∀ i, ∑ j, c i j ≤ p i) :
    ∑ i, ∑ j, completionWeight p q c i j = 1 := by
  simp only [completionWeight_row p q c hp hq hr]
  exact hp

/-- Exact marginal PMF constructed from any finite common subcoupling. -/
def completionPMF (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (hc : ∀ i j, 0 ≤ c i j)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j) : PMF (I × J) :=
  PMF.ofFintype (fun ij => ENNReal.ofReal (completionWeight p q c ij.1 ij.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ij _ => completionWeight_nonneg p q c hp hc hr hs ij.1 ij.2),
      Fintype.sum_prod_type, completionWeight_sum p q c hp hq hr, ENNReal.ofReal_one])

@[simp] theorem completionPMF_toReal (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (hc : ∀ i j, 0 ≤ c i j)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j) (ij : I × J) :
    (completionPMF p q c hp hq hc hr hs ij).toReal = completionWeight p q c ij.1 ij.2 :=
  ENNReal.toReal_ofReal (completionWeight_nonneg p q c hp hc hr hs ij.1 ij.2)

theorem completionPMF_map_fst (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (hc : ∀ i j, 0 ≤ c i j)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j) (i : I) :
    ((completionPMF p q c hp hq hc hr hs).map Prod.fst) i = ENNReal.ofReal (p i) := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    completionPMF, PMF.ofFintype_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => completionWeight_nonneg p q c hp hc hr hs i j),
    completionWeight_row p q c hp hq hr]

theorem completionPMF_map_snd (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (hc : ∀ i j, 0 ≤ c i j)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j) (j : J) :
    ((completionPMF p q c hp hq hc hr hs).map Prod.snd) j = ENNReal.ofReal (q j) := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    completionPMF, PMF.ofFintype_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => completionWeight_nonneg p q c hp hc hr hs i j),
    completionWeight_col p q c hp hq hs]

theorem completionWeight_sub_nonneg (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j) (i : I) (j : J) :
    0 ≤ completionWeight p q c i j - c i j := by
  change 0 ≤ c i j + _ - c i j
  rw [add_sub_cancel_left]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (hr i)) (sub_nonneg.mpr (hs j)))
    (sub_nonneg.mpr (commonMass_le_one p c hp hr))

theorem completionWeight_residual_mass (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) (hr : ∀ i, ∑ j, c i j ≤ p i) :
    ∑ i, ∑ j, (completionWeight p q c i j - c i j) = 1-commonMass c := by
  simp only [Finset.sum_sub_distrib, completionWeight_sum p q c hp hq hr, commonMass]

theorem completionWeight_event_le (p : I → ℝ) (q : J → ℝ) (c : I → J → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1)
    (hr : ∀ i, ∑ j, c i j ≤ p i) (hs : ∀ j, ∑ i, c i j ≤ q j)
    (P : I → J → Prop) [∀ i j, Decidable (P i j)] :
    (∑ i, ∑ j, if P i j then completionWeight p q c i j else 0) ≤
      (∑ i, ∑ j, if P i j then c i j else 0) + (1-commonMass c) := by
  classical
  have he (i : I) (j : J) :
      (if P i j then completionWeight p q c i j else 0) =
      (if P i j then c i j else 0) +
        (if P i j then completionWeight p q c i j-c i j else 0) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_add_distrib]
  apply add_le_add_right
  rw [← completionWeight_residual_mass p q c hp hq hr]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact completionWeight_sub_nonneg p q c hp hr hs i j

end Cloning.YoungFlatCoupling
