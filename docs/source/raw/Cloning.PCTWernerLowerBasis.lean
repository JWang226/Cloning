import Cloning.PCTRankAdaptedFactor
import Cloning.PCTWernerCovariance

/-! The vacuum term of the actual finite Werner output gives an operator
lower bound, valid before tracing out any environment. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.GeneralSymmetricOccupation Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem label_eq_zero_iff {L s : ℕ} (w : Word L (s+1)) :
    label w=label (fun _ : Fin L => (0:Fin (s+1))) ↔ w=(fun _ => 0) := by
  constructor
  · intro h
    obtain ⟨σ,hσ⟩ := (label_eq_iff_perm w (fun _ => 0)).mp h
    funext i
    exact (hσ i).symm
  · rintro rfl
    rfl

theorem zero_column {L s : ℕ} :
    column (label (fun _ : Fin L => (0:Fin (s+1)))) = lp.single 2 (fun _ => 0) 1 := by
  have hm : multiplicity (label (fun _ : Fin L => (0:Fin (s+1))))=1 := by
    have he : Finset.univ.filter (fun w : Word L (s+1) =>
        label w=label (fun _ => 0))={fun _ => 0} := by
      ext w
      simp [label_eq_zero_iff]
    change (Finset.univ.filter (fun w : Word L (s+1) =>
      label w=label (fun _ => 0))).card=1
    rw [he]
    simp
  apply lp.ext
  funext w
  simp [column_apply,hm,label_eq_zero_iff,lp.single_apply,Pi.single_apply,eq_comm]

/-- The actual positive Werner operator dominates its pure-product vacuum
component by the finite symmetric-dimension ratio. -/
theorem wernerOutput_vacuum_lower {L s : ℕ} (S : Finset (Fin L)) :
    (wernerScale S.card L s : ℂ) •
      (vectorProjector (lp.single 2 (fun _ : Fin L => (0:Fin (s+1))) 1)).1 ≤
      (wernerOutput (s:=s) S).1 := by
  let q0 : Occupation L (s+1) := label (fun _ => 0)
  let c : Occupation L (s+1) → ℝ := fun q =>
    ((q.val 0).choose S.card : ℝ)/(L+s).choose (S.card+s)
  have hq : q0.val 0=L := by simp [q0,label,profile]
  have hc : c q0=wernerScale S.card L s := by
    dsimp only [c]
    rw [hq,wernerScale_eq_vacuum S.card L s (by simpa using Finset.card_le_univ S)]
    rfl
  have hpos (q : Occupation L (s+1)) :
      0 ≤ (c q : ℂ) • (vectorProjector (column q)).1 := by
    change 0 ≤ (c q : ℂ) • InnerProductSpace.rankOne ℂ (column q) (column q)
    rw [Complex.coe_smul]
    exact smul_nonneg (by dsimp [c]; positivity)
      ((InnerProductSpace.rankOne ℂ (column q) (column q)).nonneg_iff_isPositive.mpr
        (InnerProductSpace.isPositive_rankOne_self (column q)))
  have hs := Finset.single_le_sum (fun q (_ : q∈Finset.univ) => hpos q)
    (Finset.mem_univ q0)
  change (c q0 : ℂ) • (vectorProjector (column q0)).1 ≤
    ∑ q, (c q : ℂ) • (vectorProjector (column q)).1 at hs
  rw [hc] at hs
  change (wernerScale S.card L s : ℂ) •
    (vectorProjector (column (label (fun _ => 0)))).1 ≤ _ at hs
  rw [zero_column] at hs
  change _ ≤ inclusionCLM (wernerOutput (s:=s) S)
  simpa only [wernerOutput,map_sum,map_smul] using hs

end Cloning.PCTRankAdapted
