import Cloning.PBWSymmetricFrameRatePhysical
import Cloning.PBWSymmetricFrameRateWeightSpace

/-! Symmetric ONBs of the actual exact Cartan-weight blocks, with one
`N⁻¹/²` constant and one threshold for every block of retained height. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.TensorLie
open PBWSymmetricFrame Cloning.PCT
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

theorem length_le_loweringHeight (w : List (PositiveRoot d)) : w.length≤loweringHeight w := by
  induction w with
  | nil => rfl
  | cons a w ih => have := a.height_pos; simp only [List.length_cons,loweringHeight]; omega

def weightRawFrame (mu : Fin d→ℕ) (hmu : Antitone mu) (R : ℕ) (η : Fin d→ℤ)
    (k : WeightOccupation d R η) : TensorRegister (∑a,mu a) (Fin d) :=
  normalizedLoweringWord (partitionHighestTensor mu hmu) mu (canonicalWord k.val.val)

def weightSymmetricFrame (mu : Fin d→ℕ) (hmu : Antitone mu) (R : ℕ) (η : Fin d→ℤ) :
    WeightOccupation d R η→TensorRegister (∑a,mu a) (Fin d) :=
  by classical exact symmetricFrame (weightRawFrame mu hmu R η)

theorem weightRawFrame_span (mu : Fin d→ℕ) (hmu : Antitone mu)
    (hgap : ∀a : PositiveRoot d,0<rootGap mu a)
    (R : ℕ) (η : Fin d→ℤ) (hη : ∑a,(a.val:ℤ)*η a≤(R:ℤ)) :
    Submodule.span ℂ (Set.range (weightRawFrame mu hmu R η))=
      cyclicSector (partitionHighestTensor mu hmu) ⊓ cartanWeightSpace (∑a,mu a) mu η := by
  rw [cyclicWeight_eq_cutoffWeight _ mu (partitionHighestTensor_cartan mu hmu) R η hη,
    canonicalWeight_span _ mu (partitionHighestTensor_cartan mu hmu) R η]
  exact span_normalizedLoweringWord_eq _ mu hgap _

theorem weightSymmetricFrame_cartan (mu : Fin d→ℕ) (hmu : Antitone mu)
    (R : ℕ) (η : Fin d→ℤ) (k : WeightOccupation d R η) (a : Fin d) :
    collectiveGenerator (∑a,mu a) a a (weightSymmetricFrame mu hmu R η k)=
      ((mu a:ℂ)+(η a:ℂ)) • weightSymmetricFrame mu hmu R η k := by
  classical
  unfold weightSymmetricFrame symmetricFrame
  simp only [map_sum,map_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [weightRawFrame,cartan_normalizedLoweringWord _ mu
    (partitionHighestTensor_cartan mu hmu),j.property,smul_comm]

/-- Uniform exact-weight version of the appendix PBW lemma. The finite
dimensional Hilbert space, Gram inverse, ONB, completeness, and quantitative
error all refer to the literal physical sector. -/
theorem eventually_weightSymmetricBasis_rate (R : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu : Fin d→ℕ) (hmu : Antitone mu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      ∀ (η : Fin d→ℤ), (∑a,(a.val:ℤ)*η a≤(R:ℤ)) →
      ∃ b : OrthonormalBasis (WeightOccupation d R η) ℂ
        ↥(cyclicSector (partitionHighestTensor mu hmu) ⊓ cartanWeightSpace (∑a,mu a) mu η),
        (∀i,(b i : TensorRegister (∑a,mu a) (Fin d))=weightSymmetricFrame mu hmu R η i) ∧
        ∀i,‖weightSymmetricFrame mu hmu R η i-weightRawFrame mu hmu R η i‖≤
          C/Real.sqrt (N:ℝ) := by
  classical
  let words : HeightOccupation d R→List (PositiveRoot d) := fun k=>canonicalWord k.val
  have hwords : ∀i j,(words i).Perm (words j)↔i=j := by
    intro i j
    simp only [words,canonicalWord_perm_iff,Subtype.val_inj]
  have hlen : ∀i,(words i).length≤R := fun i=>
    (length_le_loweringHeight _).trans (by rw [canonicalWord_height]; exact i.property)
  let A := wordGramConstant R words*rootErrorRateConstant (R*d)/Real.sqrt c
  let D : ℝ := Fintype.card (HeightOccupation d R)
  let C := D^2*A
  have hA : 0≤A := div_nonneg
    (mul_nonneg (wordGramConstant_nonneg _ _) (rootErrorRateConstant_nonneg _))
    (Real.sqrt_nonneg c)
  have hC : 0≤C := mul_nonneg (sq_nonneg _) hA
  have hN : Tendsto (fun N : ℕ=>c*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hz : Tendsto (fun N : ℕ=>C/Real.sqrt (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨C,hC,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (max 1 (2*((((R*d:ℕ):ℝ))+1)))),
    hz.eventually (eventually_lt_nhds zero_lt_one)] with N hlarge hsmall
  intro mu hmu hgap η hη
  have hpos : ∀a : PositiveRoot d,0<rootGap mu a := fun a=>
    (by have := (le_max_left _ _).trans hlarge; linarith : 0<c*(N:ℝ)).trans_le (hgap a)
  let v := weightRawFrame mu hmu R η
  have herr : ∀i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤A/Real.sqrt (N:ℝ) := by
    intro i j
    have h := physical_words_gram_error_le R words hwords hlen mu hmu
      ((le_max_right _ _).trans hlarge) hgap i.val j.val
    have he : (i.val=j.val)↔i=j := Subtype.val_inj
    rw [he] at h
    apply h.trans
    apply (mul_le_mul_of_nonneg_left
      (rootError_le_div_sqrt (R*d) ((le_max_left _ _).trans hlarge))
      (wordGramConstant_nonneg _ _)).trans_eq
    rw [Real.sqrt_mul hc.le]
    dsimp only [A]
    ring
  have hcard : (Fintype.card (WeightOccupation d R η):ℝ)≤D := by
    dsimp only [D]
    exact_mod_cast Fintype.card_le_of_injective
      (fun k : WeightOccupation d R η=>k.val) Subtype.val_injective
  have hbound : (Fintype.card (WeightOccupation d R η):ℝ)^2*(A/Real.sqrt (N:ℝ))≤
      C/Real.sqrt (N:ℝ) := by
    dsimp only [C]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hA (Real.sqrt_nonneg _))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  obtain ⟨hon,hspan,he⟩ := symmetricFrame_properties v _ herr (hbound.trans_lt hsmall)
  have hs : Submodule.span ℂ (Set.range (symmetricFrame v))=
      cyclicSector (partitionHighestTensor mu hmu) ⊓ cartanWeightSpace (∑a,mu a) mu η :=
    hspan.trans (weightRawFrame_span mu hmu hpos R η hη)
  let S := cyclicSector (partitionHighestTensor mu hmu) ⊓ cartanWeightSpace (∑a,mu a) mu η
  have hm (i : WeightOccupation d R η) : symmetricFrame v i∈S :=
    hs.le (Submodule.subset_span (Set.mem_range_self i))
  let f : WeightOccupation d R η→S := fun i=>⟨symmetricFrame v i,hm i⟩
  have hf : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    exact orthonormal_iff_ite.mp hon
  have hfs : Submodule.span ℂ (Set.range f)=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S hm).mpr hs
  let b : OrthonormalBasis (WeightOccupation d R η) ℂ S := OrthonormalBasis.mk hf hfs.ge
  refine ⟨b,fun i=>?_,fun i=>?_⟩
  · have hb : b i = f i := congrFun (OrthonormalBasis.coe_mk hf hfs.ge) i
    exact congrArg (fun x : S => (x : TensorRegister (∑a,mu a) (Fin d))) hb
  · exact (he i).trans hbound

end Cloning.TensorLie
