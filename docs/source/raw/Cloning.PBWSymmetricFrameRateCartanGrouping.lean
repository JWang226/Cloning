import Cloning.PBWSymmetricFrameRateCartanBounds

/-! Exact finite-binomial grouping of the Cartan coproduct for ordered PBW
words. The grouped amplitudes are the oscillator product amplitudes at the
finite root-gap fractions. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

local instance : DecidableEq (PositiveRoot d → ℕ) := Classical.decEq _

/-- Within the ordered coproduct the left occupation determines both words. -/
theorem loweringSplits_left_counts_injective (w : List (PositiveRoot d))
    (hw : RootOrdered w)
    (ab cd : List (PositiveRoot d) × List (PositiveRoot d))
    (hab : ab∈loweringSplits w) (hcd : cd∈loweringSplits w)
    (hcounts : (fun a => ab.1.count a) = (fun a => cd.1.count a)) : ab=cd := by
  obtain ⟨hao,hbo⟩ := loweringSplits_ordered w hw ab.1 ab.2 hab
  obtain ⟨hco,hdo⟩ := loweringSplits_ordered w hw cd.1 cd.2 hcd
  have hright : (fun a => ab.2.count a) = (fun a => cd.2.count a) := by
    funext a
    have ha := (loweringSplits_grading w ab.1 ab.2 hab).2.2 a
    have hc := (loweringSplits_grading w cd.1 cd.2 hcd).2.2 a
    have h := congrFun hcounts a
    omega
  apply Prod.ext
  · rw [← canonicalWord_counts_of_ordered ab.1 hao,
      ← canonicalWord_counts_of_ordered cd.1 hco,hcounts]
  · rw [← canonicalWord_counts_of_ordered ab.2 hbo,
      ← canonicalWord_counts_of_ordered cd.2 hdo,hright]

/-- Exact repetition count of a word pair in the ordered coproduct. -/
theorem loweringSplits_count_eq_occupationChoices
    (w : List (PositiveRoot d)) (hw : RootOrdered w)
    (u v : List (PositiveRoot d)) (huv : (u,v)∈loweringSplits w) :
    (loweringSplits w).count (u,v) = occupationChoices w (fun a => u.count a) := by
  classical
  have he : (loweringSplits w).count (u,v) =
      ((loweringSplits w).map (fun ab => fun a => ab.1.count a)).count
        (fun a => u.count a) := by
    simp only [List.count,List.countP_map]
    apply List.countP_congr
    intro ab hab
    simp only [Function.comp_def,beq_iff_eq]
    exact ⟨fun h => by cases h; rfl,
      fun h => loweringSplits_left_counts_injective w hw ab (u,v) hab huv h⟩
  rw [he,loweringSplits_count_left_occupations]
  rfl

/-- Multiplicity times the exact finite Cartan coefficient is exactly the
product-binomial amplitude at the finite root fractions. -/
theorem occupationChoices_mul_normalizedSplitCoefficient
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnu : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w u v : List (PositiveRoot d)) (h : (u,v)∈loweringSplits w) :
    (occupationChoices w (fun a => u.count a) : ℂ) *
      normalizedSplitCoefficient mu nu w u v =
      ((∏a : PositiveRoot d, Cloning.Occupation.splitAmplitude
        (w.count a) (u.count a) (rootFraction mu nu a) : ℝ) : ℂ) := by
  have hcounts := (loweringSplits_grading w u v h).2.2
  have hreverse : rootFraction nu mu = fun a => 1-rootFraction mu nu a := by
    funext a
    exact rootFraction_reverse mu nu a (ne_of_gt (add_pos (hmu a) (hnu a)))
  rw [normalizedSplitCoefficient_eq_amplitudes mu nu hmu hnu w u v h,hreverse]
  rw [← occupationSplitMatrixElement_eq_choices (rootFraction mu nu) w u v hcounts]
  exact occupationSplitMatrixElement_eq_product_amplitude (rootFraction mu nu)
    (fun a => (rootFraction_mem_Icc mu nu a (hmu a) (hnu a)).1)
    (fun a => (rootFraction_mem_Icc mu nu a (hmu a) (hnu a)).2) w u v hcounts

/-- Grouping repeated root assignments gives the exact product amplitudes,
with no limiting statement and no conditions on the vector-valued summands. -/
theorem cartan_split_sum_eq_product_amplitude {H : Type*}
    [AddCommMonoid H] [Module ℂ H]
    (mu nu : Fin d → ℕ)
    (hmu : ∀ a : PositiveRoot d, 0 < rootGap mu a)
    (hnu : ∀ a : PositiveRoot d, 0 < rootGap nu a)
    (w : List (PositiveRoot d)) (hw : RootOrdered w)
    (F : (List (PositiveRoot d) × List (PositiveRoot d)) → H) :
    ((loweringSplits w).map (fun uv =>
      normalizedSplitCoefficient mu nu w uv.1 uv.2 • F uv)).sum =
    ∑uv∈(loweringSplits w).toFinset,
      ((∏a : PositiveRoot d, Cloning.Occupation.splitAmplitude
        (w.count a) (uv.1.count a) (rootFraction mu nu a) : ℝ) : ℂ) • F uv := by
  rw [Finset.sum_list_map_count]
  apply Finset.sum_congr rfl
  intro uv huv
  rcases uv with ⟨u,v⟩
  have hmem := List.mem_toFinset.mp huv
  have hcount := loweringSplits_count_eq_occupationChoices w hw u v hmem
  simp only [List.count, Bool.beq_eq_decide_eq] at hcount ⊢
  rw [hcount]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hc := occupationChoices_mul_normalizedSplitCoefficient mu nu hmu hnu w u v hmem
  simpa only [List.count, Bool.beq_eq_decide_eq] using
    congrArg (fun z : ℂ => z • F (u,v)) hc

/-- The finite support of an ordered coproduct contains exactly one word pair
for each left suboccupation. Repeated assignments affect only its coefficient. -/
theorem loweringSplits_existsUnique_suboccupation
    (w : List (PositiveRoot d)) (hw : RootOrdered w)
    (k : PositiveRoot d → ℕ) (hk : ∀a, k a≤w.count a) :
    ∃! uv : List (PositiveRoot d) × List (PositiveRoot d),
      uv∈loweringSplits w ∧ (fun a => uv.1.count a)=k := by
  classical
  have hp : 0<((loweringSplits w).map (fun uv => fun a => uv.1.count a)).count k := by
    rw [loweringSplits_count_left_occupations]
    exact Finset.prod_pos (fun a _ => Nat.choose_pos (hk a))
  obtain ⟨uv,huv,hcounts⟩ := List.mem_map.mp (List.count_pos_iff.mp hp)
  refine ⟨uv,⟨huv,hcounts⟩,?_⟩
  intro ab hab
  exact loweringSplits_left_counts_injective w hw ab uv hab.1 huv
    (hab.2.trans hcounts.symm)

/-- The unique split attached to a suboccupation consists of its canonical
word and the canonical complementary word. -/
theorem canonical_suboccupation_mem_loweringSplits
    (w : List (PositiveRoot d)) (hw : RootOrdered w)
    (k : PositiveRoot d → ℕ) (hk : ∀a, k a≤w.count a) :
    (canonicalWord k,canonicalWord (fun a => w.count a-k a))∈loweringSplits w := by
  obtain ⟨⟨u,v⟩,⟨huv,hcounts⟩,_⟩ := loweringSplits_existsUnique_suboccupation w hw k hk
  obtain ⟨huo,hvo⟩ := loweringSplits_ordered w hw u v huv
  have hu : canonicalWord k=u := by
    rw [← hcounts]
    exact canonicalWord_counts_of_ordered u huo
  have hvcounts : (fun a => v.count a)=(fun a => w.count a-k a) := by
    funext a
    have hc := (loweringSplits_grading w u v huv).2.2 a
    have he := congrFun hcounts a
    dsimp only at he
    omega
  have hv : canonicalWord (fun a => w.count a-k a)=v := by
    rw [← hvcounts]
    exact canonicalWord_counts_of_ordered v hvo
  simpa only [hu,hv] using huv

end Cloning.TensorLie
