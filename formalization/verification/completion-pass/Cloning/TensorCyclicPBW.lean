import Cloning.TensorCyclicPartition
import Cloning.TensorCyclicError
import Cloning.TensorCCRBounds

/-! Physical cyclic cutoff invariants for the normalized root operators. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem normalizedAnnihilator_zero_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a < b) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω 0) : normalizedAnnihilator n mu a b x = 0 := by
  simp only [normalizedAnnihilator, ContinuousLinearMap.smul_apply,
    raising_zero_cyclicCutoff Ω (fun i => (mu i : ℂ)) hweight hraise a b hab hx, smul_zero]

theorem normalizedAnnihilator_lowers_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (a b : Fin d) (hab : a < b) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω (r + 1)) :
    normalizedAnnihilator n mu a b x ∈ cyclicCutoff Ω r := by
  change (Real.sqrt ((mu a : ℝ) - mu b))⁻¹ • collectiveGenerator n a b x ∈ _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (cyclicCutoff Ω r).smul_mem _
    (raising_lowers_cyclicCutoff Ω (fun i => (mu i : ℂ)) hweight hraise a b hab r hx)

theorem normalizedCreator_raises_cyclicCutoff
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (a : PositiveRoot d) (r : ℕ) {x : TensorRegister n (Fin d)}
    (hx : x ∈ cyclicCutoff Ω r) :
    normalizedCreator n mu a.val.1 a.val.2 x ∈ cyclicCutoff Ω ((r + d : ℕ) : ℤ) := by
  change (Real.sqrt ((mu a.val.1 : ℝ) - mu a.val.2))⁻¹ •
    collectiveGenerator n a.val.2 a.val.1 x ∈ _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (cyclicCutoff Ω _).smul_mem _ (lowering_raises_cyclicCutoff Ω a r hx)

theorem partitionHighestTensor_inner_self (mu : Fin d → ℕ) (hmu : Antitone mu) :
    ⟪partitionHighestTensor mu hmu, partitionHighestTensor mu hmu⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, partitionHighestTensor_norm mu hmu]
  norm_num


/-- The normalized Gram estimate for literal physical roots on any actual highest
tensor. Every filtration and CCR hypothesis of the abstract PBW theorem is
proved above from the tensor generators and highest-weight identities. -/
theorem physical_normalized_gram_error_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (root : ι → PositiveRoot d) (hinj : Function.Injective root)
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hraise : ∀ a b, a < b → collectiveGenerator n a b Ω = 0)
    (hnorm : ‖Ω‖ = 1) (L : ℕ) {δ : ℝ}
    (hδ : 2 * (((L * d : ℕ) : ℝ) + 1) ≤ δ)
    (hgap : ∀ i, δ ≤ (mu (root i).val.1 : ℝ) - mu (root i).val.2)
    (u v : List ι) (hu : u.length ≤ L) (hv : v.length ≤ L) :
    ‖⟪PBW.normalizedWord
        (fun i => normalizedCreator n mu (root i).val.1 (root i).val.2) u Ω,
      PBW.normalizedWord
        (fun i => normalizedCreator n mu (root i).val.1 (root i).val.2) v Ω⟫_ℂ -
      (if u.Perm v then 1 else 0 : ℂ)‖ ≤
      (PBW.gramConstant L u.length : ℝ) *
        (Real.sqrt (((L * d : ℕ) : ℝ) + 1) * Real.sqrt 2) ^ (2 * L) * rootError (L * d) δ := by
  have hδpos : 0 < δ := by have := Nat.cast_nonneg (α := ℝ) (L * d); linarith
  apply PBW.normalized_gram_error_le_of_root_filtration
    (fun i => normalizedCreator n mu (root i).val.1 (root i).val.2)
    (fun i => normalizedAnnihilator n mu (root i).val.1 (root i).val.2)
    (fun r => cyclicCutoff Ω (r : ℤ)) (cyclicCutoff_nat_monotone Ω) Ω
    (highest_mem_cyclicCutoff_zero Ω)
    (by rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num)
    (fun i => normalized_inner_adjoint mu (root i).val.1 (root i).val.2)
    (fun i x hx => normalizedAnnihilator_zero_cyclicCutoff Ω mu hweight hraise
      (root i).val.1 (root i).val.2 (root i).property hx)
    (fun i r x hx => normalizedAnnihilator_lowers_cyclicCutoff Ω mu hweight hraise
      (root i).val.1 (root i).val.2 (root i).property r hx)
    d L
    (fun i r x hx => normalizedCreator_raises_cyclicCutoff Ω mu (root i) r hx)
    (rootError (L * d) δ) (rootError_nonneg _ _) (rootError_le_one _ hδ) _ u v hu hv
  intro i j r hr x hx
  have hpair : ((root i).val.1, (root i).val.2) = ((root j).val.1, (root j).val.2) ↔ i = j := by
    constructor
    · intro hh
      apply hinj
      exact Subtype.ext hh
    · rintro rfl
      rfl
  have hh := normalized_CCR_norm_le Ω mu hweight hraise r hx
    (root i).val.1 (root i).val.2 (root j).val.1 (root j).val.2 hδpos (hgap i) (hgap j)
  have he : (if ((root i).val.1, (root i).val.2) = ((root j).val.1, (root j).val.2)
      then (1 : ℂ) else 0) • x = (if i = j then x else 0) := by
    simp only [hpair]
    split_ifs <;> simp
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (rootError_mono hr hδpos.le) (norm_nonneg x))

/-- For an arbitrary partition, the physical normalized PBW Gram estimate has
no assumed representation or local-CCR input. The root list may omit zero-gap
blocks by selecting only roots whose weight gaps are at least `δ`. -/
theorem partition_normalized_gram_error_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (root : ι → PositiveRoot d) (hinj : Function.Injective root)
    (mu : Fin d → ℕ) (hmu : Antitone mu) (L : ℕ) {δ : ℝ}
    (hδ : 2 * (((L * d : ℕ) : ℝ) + 1) ≤ δ)
    (hgap : ∀ i, δ ≤ (mu (root i).val.1 : ℝ) - mu (root i).val.2)
    (u v : List ι) (hu : u.length ≤ L) (hv : v.length ≤ L) :
    ‖⟪PBW.normalizedWord
        (fun i => normalizedCreator (∑ j, mu j) mu (root i).val.1 (root i).val.2) u
          (partitionHighestTensor mu hmu),
      PBW.normalizedWord
        (fun i => normalizedCreator (∑ j, mu j) mu (root i).val.1 (root i).val.2) v
          (partitionHighestTensor mu hmu)⟫_ℂ -
      (if u.Perm v then 1 else 0 : ℂ)‖ ≤
      (PBW.gramConstant L u.length : ℝ) *
        (Real.sqrt (((L * d : ℕ) : ℝ) + 1) * Real.sqrt 2) ^ (2 * L) * rootError (L * d) δ :=
  physical_normalized_gram_error_le root hinj _ mu
    (partitionHighestTensor_cartan mu hmu) (partitionHighestTensor_raising_zero mu hmu)
    (partitionHighestTensor_norm mu hmu) L hδ hgap u v hu hv

end Cloning.TensorLie
