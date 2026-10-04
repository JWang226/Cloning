import Cloning.TensorFlatProjectorLaw
import Cloning.YoungUniformLocalDensity
import Cloning.YoungHookRatio
import Mathlib.Order.Fin.Basic

/-! Exact physical flat Young masses, with a continuous positive-part Vandermonde correction. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungFlat
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungMultinomial Cloning.WeylCharacter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The ordinary flat hook-times-dimension correction. -/
def flatCorrection {r : ℕ} (μ : Fin r → ℕ) : ℝ :=
  ∏ a : PositiveRoot r,
    (((μ a.val.1 : ℝ)-μ a.val.2+a.val.2.val-a.val.1.val)^2 /
      (((μ a.val.1 : ℝ)+a.val.2.val-a.val.1.val)*((a.val.2.val : ℝ)-a.val.1.val)))

/-- Positive parts enforce the actual Young support, even before taking the limit. -/
def positiveCorrection {r : ℕ} (μ : Fin r → ℕ) : ℝ :=
  ∏ a : PositiveRoot r,
    ((max ((μ a.val.1 : ℝ)-μ a.val.2+a.val.2.val-a.val.1.val) 0)^2 /
      (((μ a.val.1 : ℝ)+a.val.2.val-a.val.1.val)*((a.val.2.val : ℝ)-a.val.1.val)))

theorem flatCorrection_eq_hook_dimension {r : ℕ} (μ : Fin r → ℕ) :
    flatCorrection μ = tableauCorrection μ * dimensionProduct μ := by
  rw [tableauCorrection_eq_pair_ratios, dimensionProduct_eq_pairProduct]
  rw [← prod_positiveRoot (fun i j : Fin r ↦
      ((μ i : ℝ)-μ j+j.val-i.val)/((μ i : ℝ)+j.val-i.val)),
    ← prod_positiveRoot (fun i j : Fin r ↦
      ((μ i : ℝ)-μ j+j.val-i.val)/((j.val : ℝ)-i.val)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [div_mul_div_comm, pow_two]

theorem positiveCorrection_eq_of_antitone {r : ℕ} (μ : Fin r → ℕ) (hμ : Antitone μ) :
    positiveCorrection μ = flatCorrection μ := by
  apply Finset.prod_congr rfl
  intro a _
  have hm : (μ a.val.2 : ℝ) ≤ μ a.val.1 := by exact_mod_cast hμ a.property.le
  have hi : (a.val.1.val : ℝ) < a.val.2.val := by exact_mod_cast Fin.lt_def.mp a.property
  rw [max_eq_left (by linarith)]

theorem positiveCorrection_eq_zero_of_not_antitone {d : ℕ} (μ : Fin (d+1) → ℕ)
    (hμ : ¬ Antitone μ) : positiveCorrection μ = 0 := by
  have hh : ∃ i : Fin d, μ i.castSucc < μ i.succ := by
    simpa only [Fin.antitone_iff_succ_le, not_forall, not_le] using hμ
  obtain ⟨i, hi⟩ := hh
  let a : PositiveRoot (d+1) := ⟨(i.castSucc, i.succ), by simp⟩
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  have hc : (μ i.castSucc : ℝ) + 1 ≤ μ i.succ := by exact_mod_cast hi
  have he : (μ a.val.1 : ℝ)-μ a.val.2+a.val.2.val-a.val.1.val ≤ 0 := by
    dsimp [a]
    push_cast
    linarith
  simp only [max_eq_right he, zero_pow (by omega : 2 ≠ 0), zero_div]

/-- Exact flat mass on every actual finite shape, including all nonpartitions. -/
theorem tensorFlatYoungPMF_eq_multinomial (d N : ℕ) (μ : Shape (d+1) N)
    (hs : ∑ i, (μ i).val = N) :
    (tensorFlatYoungPMF N (d+1) (by omega) μ).toReal =
      multinomialMass N (flatSpectrum (d+1)) (fun i ↦ (μ i).val) *
        positiveCorrection (fun i ↦ (μ i).val) := by
  by_cases hμ : Antitone (fun i ↦ (μ i).val)
  · rw [tensorFlatYoungPMF_weyl N (d+1) (by omega) μ hμ hs,
      standardCount_eq_multinomial_correction _ hμ hs,
      positiveCorrection_eq_of_antitone _ hμ, flatCorrection_eq_hook_dimension]
    have hp : (∏ i : Fin (d+1), flatSpectrum (d+1) i ^ (μ i).val) =
        (1/((d+1 : ℕ) : ℝ))^N := by
      simp only [flatSpectrum, Finset.prod_pow_eq_pow_sum, hs]
    unfold multinomialMass
    rw [hp, one_div_pow, Finset.prod_inv_distrib]
    ring
  · rw [positiveCorrection_eq_zero_of_not_antitone _ hμ, mul_zero]
    rw [tensorFlatYoungPMF, tensorYoungPMF_formula]
    simp [physicalSectorCharacter, hμ]

end Cloning.YoungFlat
