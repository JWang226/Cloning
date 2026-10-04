import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! One diverging cutoff can satisfy all countably many fixed-cutoff and
integer-window requirements simultaneously. The chosen sequence is independent
of which fixed compact window is subsequently tested. -/
noncomputable section
open Filter
open scoped Classical
namespace Cloning.TensorLAN
set_option maxHeartbeats 800000

/-- Diagonal selection for any countable family of eventual requirements.
The predicate can bundle all cutoff, window, and accuracy tests through level `r`.
No new channel is chosen after a compact set is supplied. -/
theorem exists_common_diverging_cutoff (P : ℕ → ℕ → Prop)
    (hP : ∀ r, ∀ᶠ N in atTop, P N r) :
    ∃ R : ℕ → ℕ, Monotone R ∧ Tendsto R atTop atTop ∧
      (∀ N, R N ≤ N) ∧ ∀ᶠ N in atTop, ∀ r ≤ R N, P N r := by
  classical
  have hfinite (r : ℕ) : ∀ᶠ N in atTop, ∀ k ≤ r, P N k := by
    induction r with
    | zero =>
        filter_upwards [hP 0] with N hN k hk
        simpa only [Nat.le_zero.mp hk] using hN
    | succ r ih =>
        filter_upwards [ih, hP (r + 1)] with N hN hr k hk
        rcases Nat.eq_or_lt_of_le hk with rfl | hlt
        · exact hr
        · exact hN k (Nat.le_of_lt_succ hlt)
  choose threshold hthreshold using (fun r => eventually_atTop.mp (hfinite r))
  let candidates (N : ℕ) := (Finset.range (N + 1)).filter (fun r => threshold r ≤ N)
  let R (N : ℕ) := (candidates N).sup id
  have hmem (N r : ℕ) : r ∈ candidates N ↔ r ≤ N ∧ threshold r ≤ N := by
    simp only [candidates, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hmono : Monotone R := by
    intro N M hNM
    apply Finset.sup_mono
    intro r hr
    exact (hmem M r).mpr ⟨((hmem N r).mp hr).1.trans hNM,
      ((hmem N r).mp hr).2.trans hNM⟩
  have hbound (N : ℕ) : R N ≤ N := by
    apply Finset.sup_le
    intro r hr
    exact ((hmem N r).mp hr).1
  have hlarge : Tendsto R atTop atTop := by
    apply tendsto_atTop.mpr
    intro r
    filter_upwards [eventually_ge_atTop (max r (threshold r))] with N hN
    exact Finset.le_sup (f := id) ((hmem N r).mpr ⟨(le_max_left _ _).trans hN,
      (le_max_right _ _).trans hN⟩)
  refine ⟨R, hmono, hlarge, hbound, ?_⟩
  filter_upwards [eventually_ge_atTop (threshold 0)] with N hN
  have hnonempty : (candidates N).Nonempty := ⟨0, (hmem N 0).mpr ⟨Nat.zero_le _, hN⟩⟩
  have hm : R N ∈ candidates N := by
    obtain ⟨r, hr, he⟩ := Finset.sup_mem_of_nonempty (f := id) hnonempty
    change (candidates N).sup id ∈ candidates N
    simpa only [id_eq] using he ▸ hr
  exact hthreshold (R N) N ((hmem N (R N)).mp hm).2

/-- A fixed window is eventually below the common selected cutoff. -/
theorem common_cutoff_eventually_covers {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (window : ℕ) : ∀ᶠ N in atTop, window ≤ R N :=
  hR.eventually (eventually_ge_atTop window)

/-- Sequence-wise asymptotic theorems imply uniform eventual control over
varying admissible sectors. A violating sector could otherwise be selected at
every bad sample size. The reference sequence supplies admissible values at
all remaining sizes. -/
theorem eventually_uniform_of_all_sequences {A : ℕ → Type*}
    (S : ∀ N, Set (A N)) (reference : ∀ N, A N)
    (hreference : ∀ᶠ N in atTop, reference N ∈ S N)
    (P : ∀ N, A N → Prop)
    (hseq : ∀ x : ∀ N, A N, (∀ᶠ N in atTop, x N ∈ S N) → ∀ᶠ N in atTop, P N (x N)) :
    ∀ᶠ N in atTop, ∀ x ∈ S N, P N x := by
  classical
  let choice (N : ℕ) : A N := if h : ∃ x ∈ S N, ¬ P N x then Classical.choose h else reference N
  have hmem : ∀ᶠ N in atTop, choice N ∈ S N := by
    filter_upwards [hreference] with N hN
    dsimp only [choice]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact hN
  filter_upwards [hseq choice hmem] with N hN x hx
  by_contra hbad
  have hex : ∃ x ∈ S N, ¬ P N x := ⟨x, hx, hbad⟩
  have hn : ¬ P N (choice N) := by
    dsimp only [choice]
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).2
  exact hn hN

end Cloning.TensorLAN
