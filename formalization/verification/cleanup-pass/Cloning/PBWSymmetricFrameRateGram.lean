import Cloning.PBWSymmetricFrameRateBlocks

/-! Explicit `N⁻¹/²` Gram-entry estimates and invertibility for every retained
exact physical weight block, uniformly over the root-gap lower bound. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.TensorLie
open PBWSymmetricFrame
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}
local instance (R : ℕ) (η : Fin d→ℤ) : DecidableEq (WeightOccupation d R η) := Classical.decEq _

theorem eventually_weightGram_rate (R : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu : Fin d→ℕ) (hmu : Antitone mu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      ∀ (η : Fin d→ℤ),
      IsUnit (Matrix.gram ℂ (weightRawFrame mu hmu R η)) ∧
      ∀ i j : WeightOccupation d R η,
        ‖⟪weightRawFrame mu hmu R η i,weightRawFrame mu hmu R η j⟫_ℂ-
          (if i=j then 1 else 0 : ℂ)‖≤C/Real.sqrt (N:ℝ) := by
  classical
  let words : HeightOccupation d R→List (PositiveRoot d) := fun k=>canonicalWord k.val
  have hwords : ∀i j,(words i).Perm (words j)↔i=j := by
    intro i j
    simp only [words,canonicalWord_perm_iff,Subtype.val_inj]
  have hlen : ∀i,(words i).length≤R := fun i=>
    (length_le_loweringHeight _).trans (by rw [canonicalWord_height]; exact i.property)
  let C := wordGramConstant R words*rootErrorRateConstant (R*d)/Real.sqrt c
  let D : ℝ := Fintype.card (HeightOccupation d R)
  have hC : 0≤C := div_nonneg
    (mul_nonneg (wordGramConstant_nonneg _ _) (rootErrorRateConstant_nonneg _))
    (Real.sqrt_nonneg c)
  have hN : Tendsto (fun N : ℕ=>c*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hz : Tendsto (fun N : ℕ=>D^2*C/Real.sqrt (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨C,hC,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (max 1 (2*((((R*d:ℕ):ℝ))+1)))),
    hz.eventually (eventually_lt_nhds zero_lt_one)] with N hlarge hsmall
  intro mu hmu hgap η
  let v := weightRawFrame mu hmu R η
  have herr : ∀i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤C/Real.sqrt (N:ℝ) := by
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
    dsimp only [C]
    ring
  have hcard : (Fintype.card (WeightOccupation d R η):ℝ)≤D := by
    dsimp only [D]
    exact_mod_cast Fintype.card_le_of_injective
      (fun k : WeightOccupation d R η=>k.val) Subtype.val_injective
  have hbound : (Fintype.card (WeightOccupation d R η):ℝ)^2*(C/Real.sqrt (N:ℝ))≤
      D^2*C/Real.sqrt (N:ℝ) := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hC (Real.sqrt_nonneg _))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have hV := gram_isUnit_of_error (EuclideanSpace.basisFun (WeightOccupation d R η) ℂ)
    v _ herr (hbound.trans_lt hsmall)
  have h := hV.map (Matrix.toEuclideanCLM (n := WeightOccupation d R η) (𝕜 := ℂ)).symm
  rw [←toEuclideanCLM_gram v] at h
  refine ⟨?_,herr⟩
  simpa only [StarAlgEquiv.symm_apply_apply] using h

end Cloning.TensorLie
