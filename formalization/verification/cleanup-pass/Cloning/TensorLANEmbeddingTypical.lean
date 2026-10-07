import Cloning.TensorSchurDecompositionConcentration
import Cloning.TensorLANEmbeddingTotal

/-! Typical physical labels have the diverging root gaps required by the
literal sector/Fock frames, including arbitrary moving sample subsequences. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.TensorLAN
open Cloning.TensorLie Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ c > 0, ∀ i, c ≤ f i := by
  have hs (s : Finset ι) : ∃ c > 0, ∀ i ∈ s, c ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨c, hc, hs⟩ := ih
      refine ⟨min c (f a), lt_min hc (hf a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs i hi)
  obtain ⟨c, hc, hs⟩ := hs Finset.univ
  exact ⟨c, hc, fun i => hs i (Finset.mem_univ _)⟩

def TypicalLabel {d : ℕ} (N : ℕ) (p : Fin d → ℝ) (mu : Fin d → ℕ) : Prop :=
  ∀ a, |(mu a : ℝ) - (N : ℝ) * p a| < (N : ℝ) * shrinkingRadius N

/-- No shape limit is assumed: it follows from the actual shrinking-window
condition and convergence of the moving input spectrum. -/
theorem typicalLabel_ratio_tendsto {d : ℕ} (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (mu : ℕ → Fin d → ℕ)
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (hp : ∀ a, Tendsto (fun k => pN k a) atTop (𝓝 (p a)))
    (htyp : ∀ᶠ k in atTop, TypicalLabel (n k) (pN k) (mu k)) (a : Fin d) :
    Tendsto (fun k => (mu k a : ℝ) / (n k : ℝ)) atTop (𝓝 (p a)) := by
  have herr : Tendsto (fun k => (mu k a : ℝ) / (n k : ℝ) - pN k a) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_
      (shrinkingRadius_tendsto_zero.comp hn)
    filter_upwards [htyp, hn.eventually (eventually_gt_atTop 0)] with k hk hnk
    have hnreal : (0 : ℝ) < n k := by exact_mod_cast hnk
    have he : (mu k a : ℝ) / (n k : ℝ) - pN k a =
        ((mu k a : ℝ) - (n k : ℝ) * pN k a) / (n k : ℝ) := by
      field_simp
    rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hnreal]
    exact (div_lt_iff₀ hnreal).mpr (by simpa [mul_comm] using hk a) |>.le
  simpa only [sub_add_cancel, zero_add] using herr.add (hp a)

/-- One positive constant works for every root. It depends only on the
strict limiting spectrum, not on the sequence of typical labels. -/
theorem typicalLabel_uniform_root_gap {d : ℕ} (p : Fin d → ℝ) (hord : StrictAnti p) :
    ∃ c > 0, ∀ (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
      (mu : ℕ → Fin d → ℕ) (pN : ℕ → Fin d → ℝ),
      (∀ a, Tendsto (fun k => pN k a) atTop (𝓝 (p a))) →
      (∀ᶠ k in atTop, TypicalLabel (n k) (pN k) (mu k)) →
      ∀ᶠ k in atTop, ∀ a : PositiveRoot d,
        c * (n k : ℝ) ≤ (mu k a.1.1 : ℝ) - (mu k a.1.2 : ℝ) := by
  obtain ⟨c, hc, hcg⟩ := finite_positive_lower_bound
    (fun a : PositiveRoot d => p a.1.1 - p a.1.2)
    (fun a => sub_pos.mpr (hord a.2))
  refine ⟨c / 2, by positivity, ?_⟩
  intro n hn mu pN hp htyp
  have hgap : ∀ᶠ k in atTop, ∀ a : PositiveRoot d,
      c / 2 ≤ (mu k a.1.1 : ℝ) / n k - (mu k a.1.2 : ℝ) / n k := by
    apply eventually_all.mpr
    intro a
    have ht := (typicalLabel_ratio_tendsto n hn mu pN p hp htyp a.1.1).sub
      (typicalLabel_ratio_tendsto n hn mu pN p hp htyp a.1.2)
    exact (ht.eventually (eventually_gt_nhds (by linarith [hcg a]))).mono fun k hk => hk.le
  filter_upwards [hgap, hn.eventually (eventually_gt_atTop 0)] with k hk hnk a
  have hnreal : (0 : ℝ) < n k := by exact_mod_cast hnk
  have h := hk a
  rw [← sub_div] at h
  exact (le_div_iff₀ hnreal).mp h

end Cloning.TensorLAN
