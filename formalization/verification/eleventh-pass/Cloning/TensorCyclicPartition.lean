import Cloning.TensorPartitionHighest
import Cloning.TensorRootBounds

/-! The cyclic representation and local root bounds for constructed physical
highest tensors of arbitrary partitions. No representation-existence, filtration,
or local operator-bound premises remain in these endpoints. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def partitionCyclicCutoff (mu : Fin d → ℕ) (hmu : Antitone mu) (r : ℕ) :
    Submodule ℂ (TensorRegister (∑ i, mu i) (Fin d)) :=
  cyclicCutoff (partitionHighestTensor mu hmu) r

theorem partitionCyclicCutoff_monotone (mu : Fin d → ℕ) (hmu : Antitone mu) :
    Monotone (partitionCyclicCutoff mu hmu) :=
  cyclicCutoff_nat_monotone _

theorem partitionHighestTensor_mem_cyclicCutoff (mu : Fin d → ℕ) (hmu : Antitone mu) :
    partitionHighestTensor mu hmu ∈ partitionCyclicCutoff mu hmu 0 :=
  highest_mem_cyclicCutoff_zero _

theorem partitionCyclicCutoff_zero (mu : Fin d → ℕ) (hmu : Antitone mu) :
    partitionCyclicCutoff mu hmu 0 = Submodule.span ℂ {partitionHighestTensor mu hmu} :=
  cyclicCutoff_zero _

theorem partition_raising_zero_cutoff (mu : Fin d → ℕ) (hmu : Antitone mu)
    (a b : Fin d) (hab : a < b) {x : TensorRegister (∑ i, mu i) (Fin d)}
    (hx : x ∈ partitionCyclicCutoff mu hmu 0) :
    collectiveGenerator (∑ i, mu i) a b x = 0 :=
  raising_zero_cyclicCutoff _ (fun i => (mu i : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) a b hab hx

theorem partition_raising_lowers_cutoff (mu : Fin d → ℕ) (hmu : Antitone mu)
    (a b : Fin d) (hab : a < b) (r : ℕ) {x : TensorRegister (∑ i, mu i) (Fin d)}
    (hx : x ∈ partitionCyclicCutoff mu hmu (r + 1)) :
    collectiveGenerator (∑ i, mu i) a b x ∈ partitionCyclicCutoff mu hmu r :=
  raising_lowers_cyclicCutoff _ (fun i => (mu i : ℂ))
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu) a b hab r hx

theorem partition_lowering_raises_cutoff (mu : Fin d → ℕ) (hmu : Antitone mu)
    (a : PositiveRoot d) (r : ℕ) {x : TensorRegister (∑ i, mu i) (Fin d)}
    (hx : x ∈ partitionCyclicCutoff mu hmu r) :
    collectiveGenerator (∑ i, mu i) a.val.2 a.val.1 x ∈ partitionCyclicCutoff mu hmu (r + d) :=
  lowering_raises_cyclicCutoff _ a r hx

theorem partition_cartan_defect_norm_le (mu : Fin d → ℕ) (hmu : Antitone mu)
    (r : ℕ) {x : TensorRegister (∑ i, mu i) (Fin d)}
    (hx : x ∈ partitionCyclicCutoff mu hmu r) (i : Fin d) :
    ‖collectiveGenerator (∑ i, mu i) i i x - (mu i : ℂ) • x‖ ≤ (r : ℝ) * ‖x‖ :=
  cartan_defect_norm_le _ mu (partitionHighestTensor_cartan mu hmu) r hx i

theorem partition_root_norm_le (mu : Fin d → ℕ) (hmu : Antitone mu)
    (a b : Fin d) (hab : a ≠ b) (r : ℕ) {x : TensorRegister (∑ i, mu i) (Fin d)}
    (hx : x ∈ partitionCyclicCutoff mu hmu r) :
    ‖collectiveGenerator (∑ i, mu i) a b x‖ ≤
      Real.sqrt (((r : ℝ) + 1) * (|(mu a : ℝ) - mu b| + 2 * r)) * ‖x‖ :=
  root_norm_le_cyclicCutoff _ mu (partitionHighestTensor_cartan mu hmu)
    (partitionHighestTensor_raising_zero mu hmu) a b hab r hx

end Cloning.TensorLie
