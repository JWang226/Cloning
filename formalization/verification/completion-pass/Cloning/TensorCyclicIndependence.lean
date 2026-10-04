import Cloning.TensorCyclicGramLimit
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-! Finite physical PBW independence follows from the proved Gram limit. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Gram convergence to identity gives eventual linear independence even when
the ambient Hilbert space changes with the asymptotic parameter. -/
theorem eventually_linearIndependent_of_gram_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : ℕ → Type*) [∀ N, NormedAddCommGroup (H N)] [∀ N, InnerProductSpace ℂ (H N)]
    (v : ∀ N, κ → H N)
    (hgram : Tendsto (fun N => Matrix.gram ℂ (v N)) atTop (𝓝 (1 : Matrix κ κ ℂ))) :
    ∀ᶠ N in atTop, LinearIndependent ℂ (v N) := by
  have hdet : Tendsto (fun N => (Matrix.gram ℂ (v N)).det) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.det_one] using continuous_id.matrix_det.continuousAt.tendsto.comp hgram
  have hne : ∀ᶠ N in atTop, (Matrix.gram ℂ (v N)).det ≠ 0 :=
    hdet.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  filter_upwards [hne] with N hN
  apply Matrix.linearIndependent_of_posDef_gram
  apply (Matrix.posSemidef_gram ℂ (v N)).posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hN)

/-- Every fixed finite set of distinct occupation words is eventually linearly
independent in the actual physical tensor representation. Independence is a
conclusion, not an input to the local root estimates or Gram proof. -/
theorem partition_normalizedWord_eventually_linearIndependent
    {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (root : ι → PositiveRoot d) (hinj : Function.Injective root)
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ i, δ N ≤ (mu N (root i).val.1 : ℝ) - mu N (root i).val.2)
    (words : κ → List ι) (hwords : ∀ i j, (words i).Perm (words j) ↔ i = j) :
    ∀ᶠ N in atTop, LinearIndependent ℂ
      (fun i => PBW.normalizedWord
        (fun a => normalizedCreator (∑ k, mu N k) (mu N) (root a).val.1 (root a).val.2)
        (words i) (partitionHighestTensor (mu N) (hmu N))) := by
  apply eventually_linearIndependent_of_gram_tendsto
    (fun N => TensorRegister (∑ k, mu N k) (Fin d))
  simpa only [Matrix.gram_apply] using
    partition_normalized_gramMatrix_tendsto root hinj mu hmu δ hδ hgap words hwords

end Cloning.TensorLie
