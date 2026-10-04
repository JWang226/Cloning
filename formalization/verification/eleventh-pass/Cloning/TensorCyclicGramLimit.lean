import Cloning.TensorCyclicPBW

/-! Actual fixed-word bosonic Gram limits for arbitrary physical partition
tensors with diverging retained root gaps. The Hilbert spaces and partitions
may vary. No local-CCR or PBW-independence assumption is present. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fixed normalized lowering words in the actual partition tensors converge
to the bosonic occupation Gram matrix. Roots inside zero-gap blocks can be
omitted using the injective retained-root map. -/
theorem partition_normalized_gram_tendsto
    (root : ι → PositiveRoot d) (hinj : Function.Injective root)
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ i, δ N ≤ (mu N (root i).val.1 : ℝ) - mu N (root i).val.2)
    (u v : List ι) :
    Tendsto (fun N =>
      ⟪PBW.normalizedWord
          (fun i => normalizedCreator (∑ j, mu N j) (mu N) (root i).val.1 (root i).val.2) u
            (partitionHighestTensor (mu N) (hmu N)),
        PBW.normalizedWord
          (fun i => normalizedCreator (∑ j, mu N j) (mu N) (root i).val.1 (root i).val.2) v
            (partitionHighestTensor (mu N) (hmu N))⟫_ℂ)
      atTop (𝓝 (if u.Perm v then 1 else 0)) := by
  let L := max u.length v.length
  have hu : u.length ≤ L := le_max_left _ _
  have hv : v.length ≤ L := le_max_right _ _
  have hlarge : ∀ᶠ N in atTop, 2 * (((L * d : ℕ) : ℝ) + 1) ≤ δ N :=
    hδ.eventually (eventually_ge_atTop _)
  have he := (rootError_tendsto_zero (L * d) δ hδ).const_mul
    ((PBW.gramConstant L u.length : ℝ) *
      (Real.sqrt (((L * d : ℕ) : ℝ) + 1) * Real.sqrt 2) ^ (2 * L))
  simp only [mul_zero] at he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) _ he
  filter_upwards [hlarge, hgap] with N hN hgN
  exact partition_normalized_gram_error_le root hinj (mu N) (hmu N) L hN hgN u v hu hv

/-- Any fixed finite list of distinct root occupations has Gram matrix tending
to the identity, using the actual physical tensor vectors. -/
theorem partition_normalized_gramMatrix_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (root : ι → PositiveRoot d) (hinj : Function.Injective root)
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ i, δ N ≤ (mu N (root i).val.1 : ℝ) - mu N (root i).val.2)
    (words : κ → List ι) (hwords : ∀ i j, (words i).Perm (words j) ↔ i = j) :
    Tendsto (fun N => (fun i j : κ =>
      ⟪PBW.normalizedWord
          (fun a => normalizedCreator (∑ k, mu N k) (mu N) (root a).val.1 (root a).val.2)
          (words i) (partitionHighestTensor (mu N) (hmu N)),
        PBW.normalizedWord
          (fun a => normalizedCreator (∑ k, mu N k) (mu N) (root a).val.1 (root a).val.2)
          (words j) (partitionHighestTensor (mu N) (hmu N))⟫_ℂ : Matrix κ κ ℂ))
      atTop (𝓝 (1 : Matrix κ κ ℂ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [hwords i j, Matrix.one_apply] using
    partition_normalized_gram_tendsto root hinj mu hmu δ hδ hgap (words i) (words j)

end Cloning.TensorLie
