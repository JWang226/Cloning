import Cloning.TensorLANEmbeddingTypical
import Cloning.PCTTangentChartSamples
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! Uniform admissibility and convergence of the literal local spectra on
bounded tangent windows. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.TensorLAN
open Cloning.PCTLocalChart Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

def localSpectrum (p h : Fin d → ℝ) (N : ℕ) : Fin d → ℝ :=
  fun a => p a + sampleScale N * h a

theorem localSpectrum_sum (p h : Fin d → ℝ) (hs : ∑ a, p a = 1)
    (hh : ∑ a, h a = 0) (N : ℕ) : ∑ a, localSpectrum p h N a = 1 := by
  simp only [localSpectrum, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hh, mul_zero, add_zero]

/-- Every bounded sequence of local spectral parameters has the same base
spectral limit, also along arbitrary divergent sample subsequences. -/
theorem localSpectrum_tendsto_of_bounded (p : Fin d → ℝ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (h : ℕ → Fin d → ℝ) (B : ℝ)
    (hB : ∀ᶠ k in atTop, ‖h k‖ ≤ B) (a : Fin d) :
    Tendsto (fun k => localSpectrum p (h k) (n k) a) atTop (𝓝 (p a)) := by
  have ht : Tendsto (fun k => sampleScale (n k) * h k a) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [zero_mul] using (sampleScale_tendsto.comp hn).mul_const B)
    filter_upwards [hB] with k hk
    rw [norm_mul, Real.norm_of_nonneg (by unfold sampleScale; positivity)]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (h k) a).trans hk)
      (by unfold sampleScale; positivity)
  simpa only [localSpectrum, add_zero] using ht.const_add (p a)

/-- Positivity and strict order hold uniformly on any bounded tangent window;
normalization follows from its actual trace-zero condition. -/
theorem eventually_localSpectrum_admissible (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hord : StrictAnti p) (hs : ∑ a, p a = 1)
    (K : Set (Fin d → ℝ)) (hK : Bornology.IsBounded K)
    (hzero : ∀ h ∈ K, ∑ a, h a = 0) :
    ∀ᶠ N in atTop, ∀ h ∈ K,
      (∀ a, 0 < localSpectrum p h N a) ∧ StrictAnti (localSpectrum p h N) ∧
        (∑ a, localSpectrum p h N a = 1) := by
  have hbnd : ∀ a : Fin d, ∃ B > 0, ∀ h ∈ K, ‖h a‖ ≤ B := by
    intro a
    obtain ⟨B,hB,hKB⟩ := (hK.image_eval a).exists_pos_norm_le
    exact ⟨B,hB,fun h hh => hKB _ ⟨h,hh,rfl⟩⟩
  choose C hC hKC using hbnd
  let B := 1 + ∑ a, C a
  have hB : 0 < B := by
    have hc : 0 ≤ ∑ a, C a := Finset.sum_nonneg (fun a _ => (hC a).le)
    dsimp only [B]
    linarith
  have hKB : ∀ h ∈ K, ‖h‖ ≤ B := by
    intro h hh
    apply (pi_norm_le_iff_of_nonneg hB.le).mpr
    intro a
    exact (hKC a h hh).trans ((Finset.single_le_sum (fun b _ => (hC b).le)
      (Finset.mem_univ a)).trans (by dsimp [B]; linarith))
  have ht : Tendsto (fun N => sampleScale N * B) atTop (𝓝 0) := by
    simpa only [zero_mul] using sampleScale_tendsto.mul_const B
  have hpos : ∀ᶠ N in atTop, ∀ a : Fin d, sampleScale N * B < p a / 2 :=
    eventually_all.mpr fun a => ht.eventually (eventually_lt_nhds (div_pos (hp a) (by norm_num)))
  have hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      sampleScale N * B < (p a.1.1 - p a.1.2) / 4 :=
    eventually_all.mpr fun a => ht.eventually
      (eventually_lt_nhds (div_pos (sub_pos.mpr (hord a.2)) (by norm_num)))
  filter_upwards [hpos, hgap] with N hN hg h hh
  have hb (a : Fin d) : |sampleScale N * h a| ≤ sampleScale N * B := by
    rw [abs_mul, abs_of_nonneg (by unfold sampleScale; positivity)]
    exact mul_le_mul_of_nonneg_left
      ((show |h a| ≤ ‖h‖ from norm_le_pi_norm h a).trans (hKB h hh))
      (by unfold sampleScale; positivity)
  refine ⟨?_, ?_, localSpectrum_sum p h hs (hzero h hh) N⟩
  · intro a
    have ha := (abs_le.mp (hb a)).1
    dsimp only [localSpectrum]
    linarith only [hN a, ha, hp a]
  · intro a b hab
    have hg' := hg ⟨(a,b), hab⟩
    have ha := (abs_le.mp (hb a)).1
    have hb' := (abs_le.mp (hb b)).2
    dsimp only [localSpectrum]
    dsimp only at hg'
    have hpab := hord hab
    linarith only [hg', ha, hb', hpab]

end Cloning.TensorLAN
