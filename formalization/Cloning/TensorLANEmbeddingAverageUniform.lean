import Cloning.TensorLANEmbeddingStateBounds
import Cloning.TensorLANEmbeddingCopyTail
import Cloning.TensorLANEmbeddingMixtureError

/-! Compact-uniform control of the full physical copy averages, with all
atypical labels absorbed by the actual vanishing Young tail. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace
open Filter
namespace Cloning.TensorLAN
open Cloning.TensorLie Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

def physicalForwardAverage (N Q : ℕ) (r p : Fin d → ℝ) (z : PositiveRoot d → ℂ) : ℝ :=
  ∑ i : SchurCopy N d, ((recursivePhysicalDecomposition N d).get i).character r *
    physicalGibbsForwardError ((recursivePhysicalDecomposition N d).get i).weight
      ((recursivePhysicalDecomposition N d).get i).weight_antitone r p z z Q

def physicalReverseAverage (N Q : ℕ) (r p : Fin d → ℝ) (z : PositiveRoot d → ℂ) : ℝ :=
  ∑ i : SchurCopy N d, ((recursivePhysicalDecomposition N d).get i).character r *
    physicalGibbsReverseError ((recursivePhysicalDecomposition N d).get i).weight
      ((recursivePhysicalDecomposition N d).get i).weight_antitone r p z z Q

theorem exists_cutoff_uniform_physical_averages
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p) (hs : ∑ a, p a = 1)
    (B : ℝ) (K : Set (PositiveRoot d → ℂ)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ᶠ N in atTop, ∀ h : Fin d → ℝ, ‖h‖ ≤ B →
      (∑ a, h a = 0) → (∀ a, 0 < localSpectrum p h N a) →
      Antitone (localSpectrum p h N) → ∀ z ∈ K,
      physicalForwardAverage N Q (localSpectrum p h N) p z < ε ∧
      physicalReverseAverage N Q (localSpectrum p h N) p z < ε := by
  obtain ⟨Q₀,hQ₀⟩ := exists_cutoff_uniform_typical_physical_gibbs p hp hord B K hK
    (ε/4) (by positivity)
  refine ⟨Q₀,?_⟩
  intro Q hQ
  obtain ⟨N₀,hN₀⟩ := hQ₀ Q hQ
  have htail := (physicalCopyTailEnvelope_tendsto_zero d).eventually
    (eventually_lt_nhds (show 0 < ε/8 by positivity))
  filter_upwards [eventually_ge_atTop (max N₀ 1), htail] with N hN ht h hh hzero hr horder z hz
  have hs' := localSpectrum_sum p h hs hzero N
  have hw : (∑ i : SchurCopy N d, ((recursivePhysicalDecomposition N d).get i).character
      (localSpectrum p h N)) = 1 := by
    rw [sum_physical_characters _ (recursivePhysicalDecomposition_is_decomposition N d).1
      (recursivePhysicalDecomposition_is_decomposition N d).2 _ (fun a => (hr a).le), hs', one_pow]
  have hbad := physicalCopyTail_le N d ((le_max_right _ _).trans hN)
    (localSpectrum p h N) (fun a => (hr a).le) hs' horder
  have hgood (i : SchurCopy N d)
      (hi : TypicalLabel N (localSpectrum p h N) ((recursivePhysicalDecomposition N d).get i).weight) :=
    hN₀ N ((le_max_left _ _).trans hN) _
      ((recursivePhysicalDecomposition N d).get i).weight_antitone
      ((recursivePhysicalDecomposition N d).get i).weight_sum h hh z hz hi
  have hf := weighted_error_good_bad
    (fun i : SchurCopy N d => ((recursivePhysicalDecomposition N d).get i).character (localSpectrum p h N))
    (fun i => physicalGibbsForwardError ((recursivePhysicalDecomposition N d).get i).weight
      ((recursivePhysicalDecomposition N d).get i).weight_antitone (localSpectrum p h N) p z z Q)
    (fun i => PhysicalHighestTensor.character_nonneg _ _) hw
    (fun i => TypicalLabel N (localSpectrum p h N) ((recursivePhysicalDecomposition N d).get i).weight)
    (ε/4) 2 (by positivity) (by norm_num)
    (fun i hi => (hgood i hi).1.le)
    (fun i => physicalGibbsForwardError_le_two _ _ _ p hr hp hord z Q)
  have hr' := weighted_error_good_bad
    (fun i : SchurCopy N d => ((recursivePhysicalDecomposition N d).get i).character (localSpectrum p h N))
    (fun i => physicalGibbsReverseError ((recursivePhysicalDecomposition N d).get i).weight
      ((recursivePhysicalDecomposition N d).get i).weight_antitone (localSpectrum p h N) p z z Q)
    (fun i => PhysicalHighestTensor.character_nonneg _ _) hw
    (fun i => TypicalLabel N (localSpectrum p h N) ((recursivePhysicalDecomposition N d).get i).weight)
    (ε/4) 2 (by positivity) (by norm_num)
    (fun i hi => (hgood i hi).2.le)
    (fun i => physicalGibbsReverseError_le_two _ _ _ p hr hp hord z Q)
  change physicalForwardAverage N Q (localSpectrum p h N) p z ≤
    ε/4 + 2*physicalCopyTail N d (localSpectrum p h N) at hf
  change physicalReverseAverage N Q (localSpectrum p h N) p z ≤
    ε/4 + 2*physicalCopyTail N d (localSpectrum p h N) at hr'
  constructor <;> linarith

end Cloning.TensorLAN
