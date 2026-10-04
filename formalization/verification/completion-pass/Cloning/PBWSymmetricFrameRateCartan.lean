import Cloning.PBWSymmetricFrameRateWord
import Cloning.PBWSymmetricFrameRateCartanGrouping

/-! Quantitative Cartan splitting in the literal inverse-Gram PBW frames.
The physical inclusion, source and factor frames, and exact finite root-gap
coefficients are all constructed. The bound is uniform over all partitions
whose root gaps are bounded below by `c*N`. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter
namespace Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {d : ℕ}

/-- The exact finite-parameter Cartan expansion in symmetric PBW frames has
uniform `O(N⁻¹/²)` error at every fixed retained height. Repeated root assignments
are retained here; exact product-binomial grouping is a separate algebraic identity. -/
theorem eventually_cartan_symmetricFrame_rate (R : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu nu : Fin d→ℕ) (hmu : Antitone mu) (hnu : Antitone nu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap nu a) →
      ∀ k : HeightOccupation d R,
      ‖cartanAmbientInclusion mu nu hmu hnu
          (blockSymmetricSectorFrame (fun a=>mu a+nu a)
            (sumPartition_antitone mu nu hmu hnu) R k) -
        ((loweringSplits (canonicalWord k.val)).map (fun uv=>
          normalizedSplitCoefficient mu nu (canonicalWord k.val) uv.1 uv.2 •
            tensorJoin (wordSymmetricFrame mu hmu R uv.1)
              (wordSymmetricFrame nu hnu R uv.2))).sum‖≤C/Real.sqrt (N:ℝ) := by
  obtain ⟨A,hA,hframe⟩ := eventually_wordSymmetricFrame_rate (d := d) R c hc
  let C := (1+3*(2:ℝ)^R)*A
  have hC : 0≤C := mul_nonneg (by positivity) hA
  have hz : Tendsto (fun N : ℕ=>A/Real.sqrt (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨C,hC,?_⟩
  filter_upwards [hframe,hz.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop 1] with N hN hsmall hlarge
  intro mu nu hmu hnu hmuGap hnuGap k
  let e := A/Real.sqrt (N:ℝ)
  have he : 0≤e := div_nonneg hA (Real.sqrt_nonneg _)
  have hpos : 0<c*(N:ℝ) := mul_pos hc (by exact_mod_cast hlarge)
  have hμ : ∀a : PositiveRoot d,0<rootGap mu a := fun a=>hpos.trans_le (hmuGap a)
  have hν : ∀a : PositiveRoot d,0<rootGap nu a := fun a=>hpos.trans_le (hnuGap a)
  have hsum : ∀a : PositiveRoot d,c*(N:ℝ)≤rootGap (fun i=>mu i+nu i) a := by
    intro a
    rw [rootGap_add]
    exact (hmuGap a).trans (le_add_of_nonneg_right (hν a).le)
  let w := canonicalWord k.val
  have hheight : loweringHeight w≤R := by rw [canonicalWord_height]; exact k.property
  have hlength : w.length≤R := (length_le_loweringHeight w).trans hheight
  have ho : RootOrdered w := canonicalWord_ordered k.val
  have hsource := (hN (fun a=>mu a+nu a) (sumPartition_antitone mu nu hmu hnu)
    hsum w ho hheight).2
  have hiso : ‖cartanAmbientInclusion mu nu hmu hnu
        (blockSymmetricSectorFrame (fun a=>mu a+nu a)
          (sumPartition_antitone mu nu hmu hnu) R k) -
      cartanAmbientInclusion mu nu hmu hnu
        (normalizedSectorWord (partitionHighestTensor (fun a=>mu a+nu a)
          (sumPartition_antitone mu nu hmu hnu)) (fun a=>mu a+nu a) w)‖≤e := by
    rw [←map_sub,LinearIsometry.norm_map]
    simpa only [w,wordSymmetricFrame_canonical,blockSymmetricSectorFrame,
      normalizedSectorWord,Submodule.norm_coe,Submodule.coe_sub] using hsource
  have hleft (a b : List (PositiveRoot d)) (hab : (a,b)∈loweringSplits w) :
      ‖wordSymmetricFrame mu hmu R a‖=1 ∧
      ‖normalizedLoweringWord (partitionHighestTensor mu hmu) mu a-
        wordSymmetricFrame mu hmu R a‖≤e := by
    have hg := (loweringSplits_grading w a b hab).1
    have hp := hN mu hmu hmuGap a (loweringSplits_ordered w ho a b hab).1 (by omega)
    exact ⟨hp.1,by rw [norm_sub_rev]; exact hp.2⟩
  have hright (a b : List (PositiveRoot d)) (hab : (a,b)∈loweringSplits w) :
      ‖wordSymmetricFrame nu hnu R b‖=1 ∧
      ‖normalizedLoweringWord (partitionHighestTensor nu hnu) nu b-
        wordSymmetricFrame nu hnu R b‖≤e := by
    have hg := (loweringSplits_grading w a b hab).1
    have hp := hN nu hnu hnuGap b (loweringSplits_ordered w ho a b hab).2 (by omega)
    exact ⟨hp.1,by rw [norm_sub_rev]; exact hp.2⟩
  have hsplit := cartan_split_tensor_replacement_le mu nu hμ hν w hlength
    (normalizedLoweringWord (partitionHighestTensor mu hmu) mu)
    (wordSymmetricFrame mu hmu R)
    (normalizedLoweringWord (partitionHighestTensor nu hnu) nu)
    (wordSymmetricFrame nu hnu R) e he
    (fun a b h=>(hleft a b h).1) (fun a b h=>(hright a b h).1)
    (fun a b h=>(hleft a b h).2) (fun a b h=>(hright a b h).2)
  have hsecond : ‖cartanAmbientInclusion mu nu hmu hnu
      (normalizedSectorWord (partitionHighestTensor (fun a=>mu a+nu a)
        (sumPartition_antitone mu nu hmu hnu)) (fun a=>mu a+nu a) w)-
      ((loweringSplits w).map (fun uv=>normalizedSplitCoefficient mu nu w uv.1 uv.2 •
        tensorJoin (wordSymmetricFrame mu hmu R uv.1)
          (wordSymmetricFrame nu hnu R uv.2))).sum‖≤(2:ℝ)^R*(e*(2+e)) := by
    rw [cartanAmbientInclusion_word_split mu nu hmu hnu hμ hν]
    exact hsplit
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hiso hsecond) |>.trans
  have hpow : 0≤(2:ℝ)^R := by positivity
  have hes : e≤1 := le_of_lt hsmall
  have hmul : e*(2+e)≤3*e := by nlinarith
  calc
    e+(2:ℝ)^R*(e*(2+e))≤e+(2:ℝ)^R*(3*e) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hmul hpow)
    _ = C/Real.sqrt (N:ℝ) := by dsimp only [C,e]; ring

/-- The manuscript's finite product-binomial Cartan expansion, with literal
symmetric inverse-Gram frames and a uniform physical `O(N⁻¹/²)` norm error. -/
theorem eventually_cartan_symmetricFrame_product_rate (R : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ (N : ℕ) in atTop,
      ∀ (mu nu : Fin d→ℕ) (hmu : Antitone mu) (hnu : Antitone nu),
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap mu a) →
      (∀ a : PositiveRoot d,c*(N:ℝ)≤rootGap nu a) →
      ∀ k : HeightOccupation d R,
      ‖cartanAmbientInclusion mu nu hmu hnu
          (blockSymmetricSectorFrame (fun a=>mu a+nu a)
            (sumPartition_antitone mu nu hmu hnu) R k) -
        ∑uv∈(loweringSplits (canonicalWord k.val)).toFinset,
          ((∏a : PositiveRoot d,Cloning.Occupation.splitAmplitude
            (canonicalWord k.val |>.count a) (uv.1.count a) (rootFraction mu nu a) : ℝ) : ℂ) •
            tensorJoin (wordSymmetricFrame mu hmu R uv.1)
              (wordSymmetricFrame nu hnu R uv.2)‖≤C/Real.sqrt (N:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventually_cartan_symmetricFrame_rate (d := d) R c hc
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with N hN hlarge
  intro mu nu hmu hnu hmuGap hnuGap k
  have hpos : 0<c*(N:ℝ) := mul_pos hc (by exact_mod_cast hlarge)
  have hμ : ∀a : PositiveRoot d,0<rootGap mu a := fun a=>hpos.trans_le (hmuGap a)
  have hν : ∀a : PositiveRoot d,0<rootGap nu a := fun a=>hpos.trans_le (hnuGap a)
  have he := hN mu nu hmu hnu hmuGap hnuGap k
  rw [cartan_split_sum_eq_product_amplitude mu nu hμ hν _ (canonicalWord_ordered _)] at he
  exact he

end Cloning.TensorLie
