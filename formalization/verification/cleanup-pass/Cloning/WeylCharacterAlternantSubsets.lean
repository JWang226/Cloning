import Cloning.WeylCharacterAlternantDominance
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fintype

/-! Subset sums and permutation-invariant dominance for shifted weights. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.WeylCharacter

theorem fin_strictMono_index_le {k d : ℕ} (f : Fin k → Fin d) (hf : StrictMono f)
    (i : Fin k) : i.val ≤ (f i).val := by
  have h (j : ℕ) : ∀ hj : j < k, j ≤ (f ⟨j, hj⟩).val := by
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hlt := hf (show (⟨j, by omega⟩ : Fin k) < ⟨j+1, hj⟩ by simp)
      change (f ⟨j, _⟩).val < (f ⟨j+1, _⟩).val at hlt
      omega
  exact h i.val i.isLt

theorem partialSum_eq_sum_fin {d : ℕ} (a : Fin d → ℝ) {k : ℕ} (hk : k ≤ d) :
    partialSum (zeroExtend a) k = ∑ i : Fin k, a (Fin.castLE hk i) := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [zeroExtend, dif_pos (lt_of_lt_of_le i.isLt hk)]
  rfl

theorem sum_subset_le_prefix {d : ℕ} (a : Fin d → ℝ) (ha : Antitone a)
    (s : Finset (Fin d)) :
    ∑ i ∈ s, a i ≤ partialSum (zeroExtend a) s.card := by
  have hcard : s.card ≤ d := by simpa using Finset.card_le_univ s
  rw [partialSum_eq_sum_fin a hcard]
  conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl, Finset.sum_map]
  apply Finset.sum_le_sum
  intro i hi
  apply ha
  change i.val ≤ (s.orderEmbOfFin rfl i).val
  exact fin_strictMono_index_le _ (s.orderEmbOfFin rfl).strictMono i

def finPrefix (d k : ℕ) : Finset (Fin d) := Finset.univ.filter (fun i ↦ i.val < k)

@[simp] theorem mem_finPrefix {d k : ℕ} (i : Fin d) :
    i ∈ finPrefix d k ↔ i.val < k := by simp [finPrefix]

theorem finPrefix_eq_map {d k : ℕ} (hk : k ≤ d) :
    finPrefix d k = Finset.univ.map (Fin.castLEEmb hk) := by
  ext i
  simp only [mem_finPrefix, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · rintro ⟨j, rfl⟩
    exact j.isLt

@[simp] theorem card_finPrefix {d k : ℕ} (hk : k ≤ d) :
    (finPrefix d k).card = k := by rw [finPrefix_eq_map hk]; simp

theorem sum_finPrefix {d k : ℕ} (a : Fin d → ℝ) (hk : k ≤ d) :
    ∑ i ∈ finPrefix d k, a i = partialSum (zeroExtend a) k := by
  rw [finPrefix_eq_map hk, Finset.sum_map, partialSum_eq_sum_fin a hk]
  rfl

/-- Every subset is the image of an initial segment under an actual permutation. -/
theorem exists_perm_prefix_image {d : ℕ} (s : Finset (Fin d)) :
    ∃ σ : Equiv.Perm (Fin d), (finPrefix d s.card).image σ = s := by
  have hk : s.card ≤ d := by simpa using Finset.card_le_univ s
  let e : (finPrefix d s.card) ≃ s :=
    ((finPrefix d s.card).orderIsoOfFin (card_finPrefix hk)).toEquiv.symm.trans
      (s.orderIsoOfFin rfl).toEquiv
  refine ⟨e.extendSubtype, ?_⟩
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact e.extendSubtype_mem j hj
  · intro hi
    refine ⟨(e.symm ⟨i, hi⟩).val, (e.symm ⟨i, hi⟩).property, ?_⟩
    rw [e.extendSubtype_apply_of_mem]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)

def SubsetDominatedBy {d : ℕ} (b a : Fin d → ℝ) : Prop :=
  (∀ s : Finset (Fin d), ∑ i ∈ s, b i ≤ partialSum (zeroExtend a) s.card) ∧
    (∑ i, b i) = ∑ i, a i

theorem subsetDominatedBy_of_permutations {d : ℕ} (b a : Fin d → ℝ)
    (h : ∀ σ : Equiv.Perm (Fin d), DominatedBy (b ∘ σ) a) :
    SubsetDominatedBy b a := by
  refine ⟨?_, ?_⟩
  · intro s
    obtain ⟨σ, hσ⟩ := exists_perm_prefix_image s
    have hk : s.card ≤ d := by simpa using Finset.card_le_univ s
    have hsum : (∑ i ∈ s, b i) = partialSum (zeroExtend (b ∘ σ)) s.card := by
      conv_lhs => rw [← hσ]
      rw [Finset.sum_image (fun i hi j hj hij ↦ σ.injective hij)]
      exact sum_finPrefix (b ∘ σ) hk
    rw [hsum]
    exact (h σ).1 s.card hk
  · simpa using (h (Equiv.refl _)).2

theorem subsetDominatedBy_perm {d : ℕ} {b a : Fin d → ℝ}
    (h : SubsetDominatedBy b a) (σ : Equiv.Perm (Fin d)) :
    SubsetDominatedBy (b ∘ σ) a := by
  refine ⟨?_, ?_⟩
  · intro s
    have hsum := h.1 (s.image σ)
    rw [Finset.card_image_of_injective _ σ.injective,
      Finset.sum_image (fun i hi j hj hij ↦ σ.injective hij)] at hsum
    exact hsum
  · simpa only [Function.comp_apply, Equiv.sum_comp] using h.2

theorem subsetDominatedBy_iff_permutations {d : ℕ} (b a : Fin d → ℝ) :
    SubsetDominatedBy b a ↔ ∀ σ : Equiv.Perm (Fin d), DominatedBy (b ∘ σ) a := by
  constructor
  · intro h σ
    have hp := subsetDominatedBy_perm h σ
    refine ⟨?_, hp.2⟩
    intro k hk
    simpa only [sum_finPrefix _ hk, card_finPrefix hk] using hp.1 (finPrefix d k)
  · exact subsetDominatedBy_of_permutations b a

theorem subsetDominatedBy_add {d : ℕ} {b a δ : Fin d → ℝ}
    (h : SubsetDominatedBy b a) (hδ : Antitone δ) (σ : Equiv.Perm (Fin d)) :
    SubsetDominatedBy (fun i ↦ b i + δ (σ i)) (fun i ↦ a i + δ i) := by
  have hd : SubsetDominatedBy δ δ := ⟨sum_subset_le_prefix δ hδ, rfl⟩
  have hdp := subsetDominatedBy_perm hd σ
  refine ⟨?_, ?_⟩
  · intro s
    rw [Finset.sum_add_distrib]
    have hprefix : partialSum (zeroExtend (fun i ↦ a i + δ i)) s.card =
        partialSum (zeroExtend a) s.card + partialSum (zeroExtend δ) s.card := by
      simp only [partialSum, zeroExtend]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    rw [hprefix]
    exact add_le_add (h.1 s) (hdp.1 s)
  · simpa only [Finset.sum_add_distrib, Function.comp_apply, Equiv.sum_comp] using
      congrArg (fun x ↦ x + ∑ i, δ i) h.2

end Cloning.WeylCharacter
