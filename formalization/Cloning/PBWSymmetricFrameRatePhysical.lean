import Cloning.PBWSymmetricFrameRateMatrix
import Cloning.TensorCartanCutoffFrame

/-! Uniform `N⁻¹/²` symmetric-frame rates for literal physical PBW vectors.
Only the lower root-gap bound is needed; no Gram or frame estimate is assumed. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.TensorLie
open PBWSymmetricFrame
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def rootErrorRateConstant (r : ℕ) : ℝ :=
  2*r+Real.sqrt (((r:ℝ)+1)+2*r*((r:ℝ)+1))

theorem rootErrorRateConstant_nonneg (r : ℕ) : 0≤rootErrorRateConstant r := by
  unfold rootErrorRateConstant
  positivity

theorem rootError_le_div_sqrt (r : ℕ) {δ : ℝ} (hδ : 1≤δ) :
    rootError r δ≤rootErrorRateConstant r/Real.sqrt δ := by
  have hd : 0<δ := by linarith
  let t := δ⁻¹
  have ht0 : 0≤t := inv_nonneg.mpr hd.le
  have ht1 : t≤1 := inv_le_one_of_one_le₀ hδ
  have ht2 : t^2≤t := by nlinarith
  have hts : t≤Real.sqrt t := by
    have hs := Real.sq_sqrt ht0
    have hp := Real.sqrt_nonneg t
    nlinarith
  have hs : Real.sqrt (((r:ℝ)+1)*t+2*r*((r:ℝ)+1)*t^2)≤
      Real.sqrt (((r:ℝ)+1)+2*r*((r:ℝ)+1))*Real.sqrt t := by
    rw [←Real.sqrt_mul (by positivity : 0≤((r:ℝ)+1)+2*r*((r:ℝ)+1))]
    apply Real.sqrt_le_sqrt
    have h := mul_le_mul_of_nonneg_left ht2
      (by positivity : 0≤2*(r:ℝ)*((r:ℝ)+1))
    nlinarith
  have hf : 2*(r:ℝ)*t≤2*r*Real.sqrt t :=
    mul_le_mul_of_nonneg_left hts (by positivity)
  have hh : max (2*(r:ℝ)*t)
      (Real.sqrt (((r:ℝ)+1)*t+2*r*((r:ℝ)+1)*t^2))≤
      rootErrorRateConstant r*Real.sqrt t := by
    apply max_le
    · apply hf.trans
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg t)
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    · apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg t)
      exact le_add_of_nonneg_left (by positivity)
  simpa only [rootError,div_eq_mul_inv,inv_pow,Real.sqrt_inv,t] using hh

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordGramConstant (L : ℕ) (words : ι→List (PositiveRoot d)) : ℝ :=
  (∑ i, (PBW.gramConstant L (words i).length : ℝ))*
    (Real.sqrt (((L*d:ℕ):ℝ)+1)*Real.sqrt 2)^(2*L)

theorem wordGramConstant_nonneg (L : ℕ) (words : ι→List (PositiveRoot d)) :
    0≤wordGramConstant L words := by unfold wordGramConstant; positivity

theorem physical_words_gram_error_le (L : ℕ) (words : ι→List (PositiveRoot d))
    (hwords : ∀ i j,(words i).Perm (words j)↔i=j)
    (hlen : ∀ i,(words i).length≤L) (mu : Fin d→ℕ) (hmu : Antitone mu)
    {δ : ℝ} (hδ : 2*((((L*d:ℕ):ℝ))+1)≤δ)
    (hgap : ∀ a : PositiveRoot d,δ≤rootGap mu a) (i j : ι) :
    ‖⟪normalizedLoweringWord (partitionHighestTensor mu hmu) mu (words i),
        normalizedLoweringWord (partitionHighestTensor mu hmu) mu (words j)⟫_ℂ-
      (if i=j then 1 else 0 : ℂ)‖≤wordGramConstant L words*rootError (L*d) δ := by
  have h := partition_normalized_gram_error_le (fun a : PositiveRoot d=>a)
    Function.injective_id mu hmu L hδ hgap (words i) (words j) (hlen i) (hlen j)
  simp only [hwords i j] at h
  apply h.trans
  unfold wordGramConstant
  apply mul_le_mul_of_nonneg_right _ (rootError_nonneg _ _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (fun j _=>(Nat.cast_nonneg (PBW.gramConstant L (words j).length) : (0:ℝ)≤_)) (Finset.mem_univ i)

theorem eventually_physical_words_symmetric_rate
    (L : ℕ) (words : ι→List (PositiveRoot d))
    (hwords : ∀ i j,(words i).Perm (words j)↔i=j)
    (hlen : ∀ i,(words i).length≤L) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu : Fin d→ℕ) (hmu : Antitone mu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      let v := fun i=>normalizedLoweringWord (partitionHighestTensor mu hmu) mu (words i)
      Orthonormal ℂ (symmetricFrame v) ∧
        Submodule.span ℂ (Set.range (symmetricFrame v))=Submodule.span ℂ (Set.range v) ∧
        ∀ i,‖symmetricFrame v i-v i‖≤C/Real.sqrt (N:ℝ) := by
  let A := wordGramConstant L words*rootErrorRateConstant (L*d)/Real.sqrt c
  let C := (Fintype.card ι:ℝ)^2*A
  have hA : 0≤A := by
    dsimp only [A]
    exact div_nonneg
      (mul_nonneg (wordGramConstant_nonneg L words) (rootErrorRateConstant_nonneg _))
      (Real.sqrt_nonneg c)
  have hC : 0≤C := mul_nonneg (sq_nonneg _) hA
  have hN : Tendsto (fun N : ℕ=>c*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hz : Tendsto (fun N : ℕ=>C/Real.sqrt (N:ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨C,hC,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (max 1 (2*((((L*d:ℕ):ℝ))+1)))),
    hz.eventually (eventually_lt_nhds zero_lt_one)] with N hlarge hsmall
  intro mu hmu hgap
  let v := fun i=>normalizedLoweringWord (partitionHighestTensor mu hmu) mu (words i)
  have herr : ∀ i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤A/Real.sqrt (N:ℝ) := by
    intro i j
    apply (physical_words_gram_error_le L words hwords hlen mu hmu
      ((le_max_right _ _).trans hlarge) hgap i j).trans
    apply (mul_le_mul_of_nonneg_left
      (rootError_le_div_sqrt (L*d) ((le_max_left _ _).trans hlarge))
      (wordGramConstant_nonneg L words)).trans_eq
    rw [Real.sqrt_mul hc.le]
    dsimp only [A]
    ring
  have hsmall' : (Fintype.card ι:ℝ)^2*(A/Real.sqrt (N:ℝ))<1 := by
    simpa only [C,mul_div_assoc] using hsmall
  obtain ⟨hon,hspan,herr'⟩ := symmetricFrame_properties v _ herr hsmall'
  refine ⟨hon,hspan,fun i=>?_⟩
  simpa only [C,mul_div_assoc] using herr' i

end Cloning.TensorLie
