import Cloning.TensorSchurDecompositionTrace
import Cloning.YoungGeneralTableaux
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! The actual Young-label probability law obtained by grouping physical blocks. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.YoungGeneral
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n d : ℕ}

/-- The trace of the canonical sector. Nonpartitions have no physical sector. -/
def physicalSectorCharacter (mu : Fin d → ℕ) (p : Fin d → ℝ) : ℝ :=
  if hmu : Antitone mu then
    sectorPartitionFunction (partitionHighestTensor mu hmu) mu
      (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) p
  else 0

theorem physicalSectorCharacter_nonneg (mu : Fin d → ℕ) (p : Fin d → ℝ) :
    0 ≤ physicalSectorCharacter mu p := by
  unfold physicalSectorCharacter
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem PhysicalHighestTensor.character_eq_physicalSectorCharacter
    (H : PhysicalHighestTensor n d) (p : Fin d → ℝ) :
    H.character p = physicalSectorCharacter H.weight p := by
  simp [physicalSectorCharacter, H.weight_antitone, PhysicalHighestTensor.character]

/-- Actual multiplicity in an exhaustive physical list; no combinatorial
identification enters its definition. -/
def physicalCopyCount (L : List (PhysicalHighestTensor n d)) (mu : Fin d → ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin L.length => (L.get i).weight = mu)).card

def physicalLabelMass (L : List (PhysicalHighestTensor n d)) (p : Fin d → ℝ)
    (mu : Fin d → ℕ) : ℝ :=
  ∑ i : Fin L.length, if (L.get i).weight = mu then (L.get i).character p else 0

theorem physicalLabelMass_nonneg (L : List (PhysicalHighestTensor n d))
    (p : Fin d → ℝ) (mu : Fin d → ℕ) : 0 ≤ physicalLabelMass L p mu := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact PhysicalHighestTensor.character_nonneg _ _
  · exact le_rfl

theorem physicalLabelMass_eq_count_mul (L : List (PhysicalHighestTensor n d))
    (p : Fin d → ℝ) (mu : Fin d → ℕ) :
    physicalLabelMass L p mu = (physicalCopyCount L mu : ℝ) * physicalSectorCharacter mu p := by
  unfold physicalLabelMass
  rw [← Finset.sum_filter]
  have he : ∀ i ∈ Finset.univ.filter (fun i : Fin L.length => (L.get i).weight = mu),
      (L.get i).character p = physicalSectorCharacter mu p := by
    intro i hi
    rw [PhysicalHighestTensor.character_eq_physicalSectorCharacter,
      (Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem physicalCopyCount_eq_zero_of_not_partition (L : List (PhysicalHighestTensor n d))
    (mu : Fin d → ℕ) (hmu : ¬ Antitone mu ∨ (∑ a, mu a) ≠ n) :
    physicalCopyCount L mu = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _ he
  rcases hmu with hmu | hmu
  · exact hmu (he ▸ (L.get i).weight_antitone)
  · exact hmu (he ▸ (L.get i).weight_sum)

def PhysicalHighestTensor.shape (H : PhysicalHighestTensor n d) : Shape d n :=
  fun a => ⟨H.weight a, Nat.lt_succ_of_le (by
    have h := Finset.single_le_sum (fun (b : Fin d) _ => Nat.zero_le (H.weight b))
      (Finset.mem_univ a)
    exact h.trans_eq H.weight_sum)⟩

theorem PhysicalHighestTensor.shape_eq_iff (H : PhysicalHighestTensor n d) (mu : Shape d n) :
    H.shape = mu ↔ H.weight = fun a => (mu a).val := by
  constructor
  · intro h
    exact funext (fun a => congrArg Fin.val (congrFun h a))
  · intro h
    exact funext (fun a => Fin.ext (congrFun h a))

theorem sum_physicalLabelMass (L : List (PhysicalHighestTensor n d)) (p : Fin d → ℝ) :
    ∑ mu : Shape d n, physicalLabelMass L p (fun a => (mu a).val) =
      ∑ i : Fin L.length, (L.get i).character p := by
  unfold physicalLabelMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← PhysicalHighestTensor.shape_eq_iff]
  simp

variable (L : List (PhysicalHighestTensor n d))
  (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
    (fun i => (L.get i).sector.subtypeₗᵢ))
  (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤)
  (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)

/-- This PMF is normalized by the trace of the literal tensor-power state. -/
def physicalYoungPMF : PMF (Shape d n) :=
  PMF.ofFintype (fun mu => ENNReal.ofReal (physicalLabelMass L p (fun a => (mu a).val))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun mu _ => physicalLabelMass_nonneg L p _),
      sum_physicalLabelMass, sum_physical_characters L hL hspan p hp, hs, one_pow]
    exact ENNReal.ofReal_one)

@[simp] theorem physicalYoungPMF_toReal (mu : Shape d n) :
    (physicalYoungPMF L hL hspan p hp hs mu).toReal =
      (physicalCopyCount L (fun a => (mu a).val) : ℝ) *
        physicalSectorCharacter (fun a => (mu a).val) p := by
  rw [physicalYoungPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (physicalLabelMass_nonneg L p _), physicalLabelMass_eq_count_mul]

theorem physicalYoungPMF_eq_zero_of_not_partition (mu : Shape d n)
    (hmu : ¬ Antitone (fun a => (mu a).val) ∨ (∑ a, (mu a).val) ≠ n) :
    physicalYoungPMF L hL hspan p hp hs mu = 0 := by
  rw [physicalYoungPMF, PMF.ofFintype_apply, physicalLabelMass_eq_count_mul,
    physicalCopyCount_eq_zero_of_not_partition L _ hmu, Nat.cast_zero, zero_mul,
    ENNReal.ofReal_zero]

end Cloning.TensorLie
