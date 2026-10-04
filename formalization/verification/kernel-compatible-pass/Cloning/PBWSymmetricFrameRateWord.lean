import Cloning.PBWSymmetricFrameRateBlocks

/-! A common notation for the literal exact-weight symmetric PBW frames,
indexed by retained occupations or by their canonical ordered words. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.TensorLie
open PBWSymmetricFrame
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

def blockSymmetricFrame (mu : Fin d→ℕ) (hmu : Antitone mu) (R : ℕ)
    (k : HeightOccupation d R) : TensorRegister (∑a,mu a) (Fin d) :=
  weightSymmetricFrame mu hmu R (loweringWeight (canonicalWord k.val)) ⟨k,rfl⟩

theorem blockSymmetricFrame_mem (mu : Fin d→ℕ) (hmu : Antitone mu) (R : ℕ)
    (k : HeightOccupation d R) :
    blockSymmetricFrame mu hmu R k∈cyclicSector (partitionHighestTensor mu hmu) := by
  classical
  unfold blockSymmetricFrame weightSymmetricFrame symmetricFrame
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact (normalizedSectorWord _ _ _).property

def blockSymmetricSectorFrame (mu : Fin d→ℕ) (hmu : Antitone mu) (R : ℕ)
    (k : HeightOccupation d R) : cyclicSector (partitionHighestTensor mu hmu) :=
  ⟨blockSymmetricFrame mu hmu R k,blockSymmetricFrame_mem mu hmu R k⟩

def wordOccupation (R : ℕ) (w : List (PositiveRoot d)) (hw : loweringHeight w≤R) :
    HeightOccupation d R :=
  ⟨fun a=>w.count a,by simpa only [occupationHeight,←loweringHeight_eq_sum_count] using hw⟩

@[simp] theorem canonicalWord_wordOccupation (R : ℕ) (w : List (PositiveRoot d))
    (hw : loweringHeight w≤R) (ho : RootOrdered w) :
    canonicalWord (wordOccupation R w hw).val=w := canonicalWord_counts_of_ordered w ho

/-- Total extension used solely to express finite sums over exact root assignments. -/
def wordSymmetricFrame (mu : Fin d→ℕ) (hmu : Antitone mu) (R : ℕ)
    (w : List (PositiveRoot d)) : TensorRegister (∑a,mu a) (Fin d) :=
  if hw : loweringHeight w≤R then blockSymmetricFrame mu hmu R (wordOccupation R w hw) else 0

@[simp] theorem wordSymmetricFrame_canonical (mu : Fin d→ℕ) (hmu : Antitone mu)
    (R : ℕ) (k : HeightOccupation d R) :
    wordSymmetricFrame mu hmu R (canonicalWord k.val)=blockSymmetricFrame mu hmu R k := by
  have hw : loweringHeight (canonicalWord k.val)≤R := by
    rw [canonicalWord_height]; exact k.property
  rw [wordSymmetricFrame,dif_pos hw]
  congr 1
  apply Subtype.ext
  funext a
  exact canonicalWord_count _ a

/-- One constant and one threshold work for every weight and every retained
occupation, in arbitrary physical partitions satisfying the lower gap bound. -/
theorem eventually_blockSymmetricFrame_rate (R : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu : Fin d→ℕ) (hmu : Antitone mu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      ∀ k : HeightOccupation d R,
      ‖blockSymmetricFrame mu hmu R k‖=1 ∧
      ‖blockSymmetricFrame mu hmu R k-
        normalizedLoweringWord (partitionHighestTensor mu hmu) mu (canonicalWord k.val)‖≤
          C/Real.sqrt (N:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventually_weightSymmetricBasis_rate (d := d) R c hc
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with N hN
  intro mu hmu hg k
  have hk : (∑ a,(a.val:ℤ)*loweringWeight (canonicalWord k.val) a)≤(R:ℤ) := by
    rw [loweringWeight_index_sum,canonicalWord_height]
    exact_mod_cast k.property
  obtain ⟨b,hb,he⟩ := hN mu hmu hg (loweringWeight (canonicalWord k.val)) hk
  refine ⟨?_,he ⟨k,rfl⟩⟩
  rw [blockSymmetricFrame,←hb ⟨k,rfl⟩]
  exact b.orthonormal.norm_eq_one ⟨k,rfl⟩

/-- Word form of the same exact-block symmetric-frame rate. -/
theorem eventually_wordSymmetricFrame_rate (R : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu : Fin d→ℕ) (hmu : Antitone mu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      ∀ w : List (PositiveRoot d), RootOrdered w → loweringHeight w≤R →
      ‖wordSymmetricFrame mu hmu R w‖=1 ∧
      ‖wordSymmetricFrame mu hmu R w-
        normalizedLoweringWord (partitionHighestTensor mu hmu) mu w‖≤
          C/Real.sqrt (N:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventually_blockSymmetricFrame_rate (d := d) R c hc
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with N hN
  intro mu hmu hg w ho hw
  have hh := hN mu hmu hg (wordOccupation R w hw)
  rw [canonicalWord_wordOccupation R w hw ho] at hh
  simpa only [wordSymmetricFrame,dif_pos hw] using hh

end Cloning.TensorLie
