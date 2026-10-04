import Cloning.YoungRounding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Compatibility of actual rounded Young labels

The difference between a typical input and every label in the support of the
actual dither kernel is a partition once the spectral gap exceeds the explicit
rounding error.  Compatibility is derived from coordinate estimates; it is not
an input assumption.  `d` denotes the number of head coordinates, so labels have
`d+1` rows.  This file does not assert concentration of the Young distribution.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology
open Filter

namespace Cloning.YoungCompatibility

/-- A nonnegative decreasing integer row vector, with its total number of boxes. -/
def IsYoung {d : ℕ} (n : ℤ) (μ : Fin d → ℤ) : Prop :=
  (∀ i, 0 ≤ μ i) ∧ Antitone μ ∧ ∑ i, μ i = n

/-- The literal Cartan compatibility condition. -/
def Compatible {d : ℕ} (n m : ℤ) (μ ν : Fin d → ℤ) : Prop :=
  IsYoung (m - n) (fun i ↦ ν i - μ i)

/-- Add the uniquely determined final lattice coordinate. -/
def complete {d : ℕ} (m : ℤ) (z : Fin d → ℤ) : Fin (d + 1) → ℤ :=
  Fin.snoc z (Rounding.completeLast m z)

@[simp] theorem complete_head {d : ℕ} (m : ℤ) (z : Fin d → ℤ) (i : Fin d) :
    complete m z i.castSucc = z i := by simp [complete]

@[simp] theorem complete_last {d : ℕ} (m : ℤ) (z : Fin d → ℤ) :
    complete m z (Fin.last d) = Rounding.completeLast m z := by simp [complete]

theorem complete_sum {d : ℕ} (m : ℤ) (z : Fin d → ℤ) :
    ∑ i, complete m z i = m := by
  rw [Fin.sum_univ_castSucc]
  simp [Rounding.completeLast]

/-- A compatible output of a Young input is a Young label. -/
theorem compatible_isYoung {d : ℕ} {n m : ℤ} {μ ν : Fin d → ℤ}
    (hμ : IsYoung n μ) (h : Compatible n m μ ν) : IsYoung m ν := by
  dsimp only [Compatible, IsYoung] at h hμ ⊢
  refine ⟨fun i ↦ by have := h.1 i; have := hμ.1 i; omega,
    fun i j hij ↦ by
      have hd : ν j - μ j ≤ ν i - μ i := h.2.1 hij
      have := hμ.2.1 hij
      omega, ?_⟩
  have hm := h.2.2
  simp only [Finset.sum_sub_distrib, hμ.2.2] at hm
  omega

/-- An explicit deterministic criterion.  A lower bound `a` for both row
probabilities and all ordered spectral gaps controls the two kinds of boundary.
The rounding error `c` is unnormalized. -/
theorem compatible_of_typical {d : ℕ} (n m : ℤ) (μ ν : Fin d → ℤ)
    (p : Fin d → ℝ) (γ ε a c : ℝ)
    (hn : 0 ≤ (n : ℝ)) (hγ : 1 ≤ γ) (ha : 0 ≤ a)
    (hp : ∀ i, a ≤ p i) (hgap : ∀ i j, i < j → a ≤ p i - p j)
    (hε : ε ≤ a / 4) (hmargin : 4 * c ≤ (γ - 1) * (n : ℝ) * a)
    (hμmass : ∑ i, μ i = n) (hνmass : ∑ i, ν i = m)
    (hμ : ∀ i, |(μ i : ℝ) - (n : ℝ) * p i| ≤ (n : ℝ) * ε)
    (hν : ∀ i, |(ν i : ℝ) - γ * (μ i : ℝ)| ≤ c) :
    Compatible n m μ ν := by
  have hγ0 : 0 ≤ γ - 1 := sub_nonneg.mpr hγ
  have hne : (n : ℝ) * ε ≤ (n : ℝ) * (a / 4) := mul_le_mul_of_nonneg_left hε hn
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := (abs_le.mp (hμ i)).1
    have hi' := (abs_le.mp (hν i)).1
    have hp' := mul_le_mul_of_nonneg_left (hp i) hn
    have hm : (n : ℝ) * (a / 2) ≤ (μ i : ℝ) := by nlinarith
    have hm' := mul_le_mul_of_nonneg_left hm hγ0
    have hna := mul_nonneg hn ha
    have hreal : 0 ≤ (ν i : ℝ) - (μ i : ℝ) := by nlinarith
    exact_mod_cast hreal
  · intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · have hi := (abs_le.mp (hμ i)).1
      have hj := (abs_le.mp (hμ j)).2
      have hi' := (abs_le.mp (hν i)).1
      have hj' := (abs_le.mp (hν j)).2
      have hp' := mul_le_mul_of_nonneg_left (hgap i j hij) hn
      have hm : (n : ℝ) * (a / 2) ≤ (μ i : ℝ) - (μ j : ℝ) := by nlinarith
      have hm' := mul_le_mul_of_nonneg_left hm hγ0
      have hreal : (ν j : ℝ) - (μ j : ℝ) ≤ (ν i : ℝ) - (μ i : ℝ) := by nlinarith
      exact_mod_cast hreal
    · exact le_rfl
  · rw [Finset.sum_sub_distrib, hμmass, hνmass]

/-- Uniform error for every full label in the actual PMF's support, including
its dependent final coordinate. -/
theorem complete_rounding_support_error {d : ℕ} (hd : 1 ≤ d)
    (n m : ℤ) (μ : Fin (d + 1) → ℤ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hμmass : ∑ i, μ i = n) (hm : (m : ℝ) = γ * (n : ℝ))
    (z : Fin d → ℤ)
    (hz : YoungRounding.roundingPMF γ (fun i ↦ (μ i.castSucc : ℝ)) z ≠ 0)
    (i : Fin (d + 1)) :
    |(complete m z i : ℝ) - γ * (μ i : ℝ)| ≤ (d : ℝ) * ((γ + 1) / 2) := by
  have hc : 0 ≤ (γ + 1) / 2 := by positivity
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hhead j := YoungRounding.roundingPMF_support γ hγ
    (fun i ↦ (μ i.castSucc : ℝ)) z hz j
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [complete_last]
    have hmass : (∑ j : Fin d, (μ j.castSucc : ℝ)) + (μ (Fin.last d) : ℝ) = n := by
      exact_mod_cast (show (∑ j : Fin d, μ j.castSucc) + μ (Fin.last d) = n by
        simpa only [Fin.sum_univ_castSucc] using hμmass)
    have hscale : (m : ℝ) = γ * ((∑ j : Fin d, (μ j.castSucc : ℝ)) + (μ (Fin.last d) : ℝ)) := by
      rw [hmass, hm]
    simpa only [Fintype.card_fin] using Rounding.completeLast_error_bound m z
      (fun i : Fin d ↦ (μ i.castSucc : ℝ)) (μ (Fin.last d)) γ ((γ + 1) / 2) hscale hhead
  · rw [complete_head]
    exact (hhead j).trans (by nlinarith)

/-- The actual dither PMF cannot leave the compatible sector on a typical input
under the explicit spectral-gap and sample-size conditions. -/
theorem rounding_support_compatible {d : ℕ} (hd : 1 ≤ d)
    (n m : ℤ) (μ : Fin (d + 1) → ℤ) (p : Fin (d + 1) → ℝ)
    (γ ε a : ℝ) (hn : 0 ≤ (n : ℝ)) (hγ : 1 ≤ γ) (ha : 0 ≤ a)
    (hp : ∀ i, a ≤ p i) (hgap : ∀ i j, i < j → a ≤ p i - p j)
    (hε : ε ≤ a / 4)
    (hmargin : 4 * ((d : ℝ) * ((γ + 1) / 2)) ≤ (γ - 1) * (n : ℝ) * a)
    (hμmass : ∑ i, μ i = n) (hm : (m : ℝ) = γ * (n : ℝ))
    (hμ : ∀ i, |(μ i : ℝ) - (n : ℝ) * p i| ≤ (n : ℝ) * ε)
    (z : Fin d → ℤ)
    (hz : YoungRounding.roundingPMF γ (fun i ↦ (μ i.castSucc : ℝ)) z ≠ 0) :
    Compatible n m μ (complete m z) :=
  compatible_of_typical n m μ (complete m z) p γ ε a _ hn hγ ha hp hgap hε
    hmargin hμmass (complete_sum m z) hμ
    (complete_rounding_support_error hd n m μ γ (by linarith) hμmass hm z hz)

/-- The deterministic thresholds hold eventually at every fixed gain above one.
The quantifiers over spectra and labels are inside the eventual quantifier, so
this is uniform over all spectra with a common positive gap. -/
theorem eventually_rounding_support_compatible {d : ℕ} (hd : 1 ≤ d)
    (m : ℕ → ℤ) (γn ε : ℕ → ℝ) (γ a : ℝ)
    (ha : 0 < a) (hγ : 1 < γ)
    (hγn : Tendsto γn atTop (𝓝 γ)) (hε : Tendsto ε atTop (𝓝 0))
    (hm : ∀ n, (m n : ℝ) = γn n * (n : ℝ)) :
    ∀ᶠ (n : ℕ) in atTop, ∀ (p : Fin (d + 1) → ℝ),
      (∀ i, a ≤ p i) → (∀ i j, i < j → a ≤ p i - p j) →
      ∀ (μ : Fin (d + 1) → ℤ), (∑ i, μ i = (n : ℤ)) →
      (∀ i, |(μ i : ℝ) - (n : ℝ) * p i| ≤ (n : ℝ) * ε n) →
      ∀ z, YoungRounding.roundingPMF (γn n) (fun i ↦ (μ i.castSucc : ℝ)) z ≠ 0 →
        Compatible (n : ℤ) (m n) μ (complete (m n) z) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hright : Tendsto (fun n ↦ (γn n - 1) * (n : ℝ) * a) atTop atTop :=
    ((hγn.sub_const 1).pos_mul_atTop (by linarith) hn).atTop_mul_pos ha tendsto_const_nhds
  have hleft : Tendsto (fun n ↦ 4 * ((d : ℝ) * ((γn n + 1) / 2))) atTop
      (𝓝 (4 * ((d : ℝ) * ((γ + 1) / 2)))) := by
    exact (((hγn.add_const 1).div_const 2).const_mul (d : ℝ)).const_mul 4
  have hleftbd := hleft.eventually (gt_mem_nhds (lt_add_one (4 * ((d : ℝ) * ((γ + 1) / 2)))))
  have hrightbd := hright.eventually (eventually_ge_atTop (4 * ((d : ℝ) * ((γ + 1) / 2)) + 1))
  have heps := hε.eventually (gt_mem_nhds (show (0 : ℝ) < a / 4 by positivity))
  have hgain := hγn.eventually (lt_mem_nhds hγ)
  filter_upwards [hleftbd, hrightbd, heps, hgain] with n hl hr he hg
  intro p hp hgap μ hmass htyp z hz
  apply rounding_support_compatible hd (n : ℤ) (m n) μ p (γn n) (ε n) a
    (by positivity) hg.le ha.le hp hgap he.le
  · exact_mod_cast hl.le.trans hr
  · exact hmass
  · simpa only [Int.cast_natCast] using hm n
  · simpa only [Int.cast_natCast] using htyp
  · exact hz

private theorem finite_positive_lower {I : Type*} [Fintype I]
    (f : I → ℝ) (hf : ∀ i, 0 < f i) : ∃ a, 0 < a ∧ ∀ i, a ≤ f i := by
  classical
  have h : ∀ s : Finset I, ∃ a, 0 < a ∧ ∀ i ∈ s, a ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, hb⟩ := ih
      refine ⟨min a (f i), lt_min ha (hf i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb j hj)
  obtain ⟨a, ha, hb⟩ := h Finset.univ
  exact ⟨a, ha, fun i ↦ hb i (Finset.mem_univ i)⟩

/-- Compact subsets of strictly decreasing positive spectra have the common
positive row and spectral-gap bounds used above.  Compactness is applied to
actual coordinate functions, with no compatibility input. -/
theorem compact_spectra_positive_gap {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, ∀ i, 0 < p i)
    (hanti : ∀ p ∈ K, StrictAnti p) :
    ∃ a, 0 < a ∧ (∀ p ∈ K, ∀ i, a ≤ p i) ∧
      (∀ p ∈ K, ∀ i j, i < j → a ≤ p i - p j) := by
  classical
  have hrow (i : Fin d) : ∃ a, 0 < a ∧ ∀ p ∈ K, a ≤ p i :=
    hK.exists_forall_le' (continuous_apply i).continuousOn (fun p hp ↦ hpos p hp i)
  choose row hrow0 hrowbd using hrow
  obtain ⟨a, ha, habd⟩ := finite_positive_lower row hrow0
  have hpair (ij : Fin d × Fin d) :
      ∃ b, 0 < b ∧ ∀ p ∈ K, ij.1 < ij.2 → b ≤ p ij.1 - p ij.2 := by
    by_cases hij : ij.1 < ij.2
    · obtain ⟨b, hb, hbd⟩ := hK.exists_forall_le'
        ((continuous_apply ij.1).sub (continuous_apply ij.2)).continuousOn
        (fun p hp ↦ sub_pos.mpr (hanti p hp hij))
      exact ⟨b, hb, fun p hp _ ↦ hbd p hp⟩
    · exact ⟨1, by norm_num, fun _ _ h ↦ (hij h).elim⟩
  choose pair hpair0 hpairbd using hpair
  obtain ⟨b, hb, hbbd⟩ := finite_positive_lower pair hpair0
  refine ⟨min a b, lt_min ha hb, ?_, ?_⟩
  · intro p hp i
    exact (min_le_left _ _).trans ((habd i).trans (hrowbd i p hp))
  · intro p hp i j hij
    exact (min_le_right _ _).trans ((hbbd (i,j)).trans (hpairbd (i,j) p hp hij))

end Cloning.YoungCompatibility
