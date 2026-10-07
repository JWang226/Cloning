import Cloning.YoungDimensionMomentRateAlgebra
import Cloning.TensorFlatProjectorCasimirMoment
import Cloning.TensorFlatProjectorMoments

/-! Quantitative forward and reciprocal dimension moments under the actual
physical flat Young law. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Cloning.TensorLie
open Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def dimensionMomentRateConstant (r k : ℕ) : ℝ :=
  globalSecondOrderConstant r k*(1+(r:ℝ))

theorem dimensionMomentRateConstant_nonneg (r k : ℕ) :
    0≤dimensionMomentRateConstant r k :=
  mul_nonneg (globalSecondOrderConstant_nonneg r k) (by positivity)

/-- A fully finite O(1/N) bound; labels outside the physical box-count
support have zero actual probability. -/
theorem tensorFlatYoungPMF_mean_dimension_error_le (r k N : ℕ) (hr : 0<r) (hN : 1≤N) :
    (∑ mu,(tensorFlatYoungPMF N r hr mu).toReal*
      |normalizedDimension r k N mu-1|) ≤ dimensionMomentRateConstant r k/(N:ℝ) := by
  let P := tensorFlatYoungPMF N r hr
  let G := globalSecondOrderConstant r k
  let V : Shape r N→ℝ := fun mu=>∑i,((mu i).val-(N:ℝ)/r)^2
  have hG : 0≤G := globalSecondOrderConstant_nonneg r k
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpoint (mu : Shape r N) :
      (P mu).toReal*|normalizedDimension r k N mu-1| ≤
        (P mu).toReal*(G*(1/(N:ℝ)+V mu/(N:ℝ)^2)) := by
    by_cases hs : ∑i,(mu i).val=N
    · exact mul_le_mul_of_nonneg_left (normalizedDimension_global_second_order r k N hr hN mu hs)
        ENNReal.toReal_nonneg
    · have hz : P mu=0 := physicalYoungPMF_eq_zero_of_not_partition
        (recursivePhysicalDecomposition N r) (recursivePhysicalDecomposition_is_decomposition N r).1
        (recursivePhysicalDecomposition_is_decomposition N r).2 (flatSpectrum r)
        (fun _=>by unfold flatSpectrum; positivity) (flatSpectrum_sum r hr) mu (Or.inr hs)
      simp only [hz,ENNReal.toReal_zero,zero_mul,le_refl]
  have hmass : ∑mu,(P mu).toReal=1 := by
    simpa only [tsum_fintype,Cloning.YoungCompatibility.probability] using
      Cloning.YoungCompatibility.tsum_probability P
  have hmoment : (∑mu,(P mu).toReal*V mu)≤(N:ℝ)*r :=
    (tensorFlatYoungPMF_centered_second_moment_le (n := N) hr).trans
      (mul_le_mul_of_nonneg_left (sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg r)))
        (Nat.cast_nonneg N))
  calc
    _ ≤ ∑mu,(P mu).toReal*(G*(1/(N:ℝ)+V mu/(N:ℝ)^2)) :=
      Finset.sum_le_sum (fun mu _=>hpoint mu)
    _ = G*(1/(N:ℝ)+(∑mu,(P mu).toReal*V mu)/(N:ℝ)^2) := by
      have he (mu : Shape r N) : (P mu).toReal*(G*(1/(N:ℝ)+V mu/(N:ℝ)^2))=
          (G/(N:ℝ))*(P mu).toReal+(G/(N:ℝ)^2)*((P mu).toReal*V mu) := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hmass]
      ring
    _ ≤ G*(1/(N:ℝ)+((N:ℝ)*r)/(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (div_le_div_of_nonneg_right hmoment (sq_nonneg (N:ℝ)))) hG
    _ = dimensionMomentRateConstant r k/(N:ℝ) := by
      unfold dimensionMomentRateConstant
      dsimp only [G]
      field_simp [hn.ne'] <;> ring

/-- On the central window, reciprocal relative error is at most twice the
forward relative error itself. -/
theorem inverseDimension_error_le_forward (r k N : ℕ) (hr : 0<r) (hN : 1≤N)
    (hsmall : dimensionErrorEnvelope r k N≤1/2) (mu : Shape r N)
    (ht : ¬∃i,(N:ℝ)*shrinkingRadius N≤|shapeRows mu i-N*flatSpectrum r i|) :
    |inverseNormalizedDimension r k N mu-1|≤2*|normalizedDimension r k N mu-1| := by
  let R := dimensionRatio r k (shapeRows mu)
  let D := leadingConstant r k*(N:ℝ)^(r*k)
  have hR : 0<R := dimensionRatio_pos r k (shapeRows mu) (shapeRows_nonneg mu)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hD : 0<D := mul_pos (leadingConstant_pos r k hr) (pow_pos hn _)
  have he : |R/D-1|≤1/2 := (normalizedDimension_typical_error r k N hr hN mu ht).trans hsmall
  have hl : (1/2:ℝ)≤R/D := by have hh := (abs_le.mp he).1; linarith
  have hl' : D≤2*R := by have hh := (le_div_iff₀ hD).mp hl; linarith
  have hi : D/R≤2 := (div_le_iff₀ hR).mpr hl'
  change |D/R-1|≤2*|R/D-1|
  have ha : D/R-1=-(D/R)*(R/D-1) := by field_simp; ring
  rw [ha,abs_mul,abs_neg,abs_of_pos (div_pos hD hR)]
  exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

theorem tensorFlatYoungPMF_mean_inverse_error_split (r k N : ℕ) (hr : 0<r) (hN : 1≤N)
    (hsmall : dimensionErrorEnvelope r k N≤1/2) :
    (∑mu,(tensorFlatYoungPMF N r hr mu).toReal*|inverseNormalizedDimension r k N mu-1|)≤
      2*(∑mu,(tensorFlatYoungPMF N r hr mu).toReal*|normalizedDimension r k N mu-1|)+
      (leadingConstant r k*(N:ℝ)^(r*k)+1)*
        tailProbability (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N) := by
  let P := tensorFlatYoungPMF N r hr
  let B := leadingConstant r k*(N:ℝ)^(r*k)+1
  have hp (mu : Shape r N) :
      (P mu).toReal*|inverseNormalizedDimension r k N mu-1|≤
        2*((P mu).toReal*|normalizedDimension r k N mu-1|)+
          B*(if ∃i,(N:ℝ)*shrinkingRadius N≤|shapeRows mu i-N*flatSpectrum r i|
            then (P mu).toReal else 0) := by
    split_ifs with ht
    · have he := mul_le_mul_of_nonneg_left
        (inverseNormalizedDimension_global_error r k N hr mu)
        (show 0≤(P mu).toReal from ENNReal.toReal_nonneg)
      have hz := mul_nonneg (show 0≤(P mu).toReal from ENNReal.toReal_nonneg)
        (abs_nonneg (normalizedDimension r k N mu-1))
      dsimp only [B]
      nlinarith
    · have he := mul_le_mul_of_nonneg_left
        (inverseDimension_error_le_forward r k N hr hN hsmall mu ht)
        (show 0≤(P mu).toReal from ENNReal.toReal_nonneg)
      simpa only [mul_zero,add_zero,mul_left_comm] using he
  have hs := Finset.sum_le_sum (fun mu (_ : mu∈Finset.univ)=>hp mu)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,tailProbability,shapeRows,P,B] using hs

/-- Even after multiplying by the worst reciprocal dimension, the physical
atypical mass is eventually bounded by 1/N. -/
theorem tensorFlatYoungPMF_reciprocal_tail_rate (r k : ℕ) (hr : 0<r) :
    ∀ᶠ (N : ℕ) in atTop,
      (leadingConstant r k*(N:ℝ)^(r*k)+1)*
        tailProbability (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N)≤1/(N:ℝ) := by
  let c := leadingConstant r k
  let a := r*k
  let s := Fintype.card (PositiveRoot r)
  let C := ((r:ℝ)+1)^s
  have hc : 0≤c := (leadingConstant_pos r k hr).le
  have hC : 0≤C := by dsimp [C]; positivity
  have ht := (polynomial_concentrationEnvelope_tendsto_zero r (a+s+1)).const_mul ((c+1)*C)
  simp only [mul_zero] at ht
  have hsmall : ∀ᶠ (N : ℕ) in atTop, ((c+1)*C)*(((N:ℝ)+1)^(a+s+1)*concentrationEnvelope r N)≤1 :=
    ht.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop 1,hsmall] with N hN hsmall
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have htail := tensorYoungPMF_tail_shrinking_le N hN (flatSpectrum r)
    (fun _=>by unfold flatSpectrum; positivity) (flatSpectrum_sum r hr) antitone_const
  have hpw : (N:ℝ)^a≤((N:ℝ)+1)^a := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpw1 : (1:ℝ)≤((N:ℝ)+1)^a := one_le_pow₀ (by linarith [(Nat.cast_nonneg N : (0:ℝ)≤N)])
  have hcoeff : c*(N:ℝ)^a+1≤(c+1)*((N:ℝ)+1)^a := by
    nlinarith [mul_le_mul_of_nonneg_left hpw hc]
  have ht0 : 0≤tailProbability (tensorFlatYoungPMF N r hr) (flatSpectrum r) (shrinkingRadius N) :=
    tensorYoungPMF_tail_nonneg _ _ _ _
  have hprod := mul_le_mul hcoeff htail ht0 (by positivity : 0≤(c+1)*((N:ℝ)+1)^a)
  have hb : (c*(N:ℝ)^a+1)*tailProbability (tensorFlatYoungPMF N r hr)
      (flatSpectrum r) (shrinkingRadius N)≤
      ((c+1)*C)*(((N:ℝ)+1)^(a+s)*concentrationEnvelope r N) := by
    convert hprod using 1 <;> dsimp only [C,s] <;> rw [pow_add] <;> ring
  have henv : 0≤((c+1)*C)*(((N:ℝ)+1)^(a+s)*concentrationEnvelope r N) := by
    unfold concentrationEnvelope
    positivity
  have hmul := mul_le_mul_of_nonneg_left hb hn.le
  have hnext := mul_le_mul_of_nonneg_right (show (N:ℝ)≤N+1 by linarith) henv
  have hs : (N:ℝ)*((c*(N:ℝ)^a+1)*tailProbability (tensorFlatYoungPMF N r hr)
      (flatSpectrum r) (shrinkingRadius N))≤1 := by
    apply hmul.trans (hnext.trans ?_)
    convert hsmall using 1
    rw [pow_succ]
    ring
  exact (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hs)

/-- Quantitative reciprocal moment control with every premise discharged for
the actual physical flat-spectrum law. -/
theorem tensorFlatYoungPMF_mean_inverse_dimension_error_le (r k : ℕ) (hr : 0<r) :
    ∀ᶠ (N : ℕ) in atTop,
      (∑mu,(tensorFlatYoungPMF N r hr mu).toReal*|inverseNormalizedDimension r k N mu-1|)≤
        (2*dimensionMomentRateConstant r k+1)/(N:ℝ) := by
  have hs : ∀ᶠ (N : ℕ) in atTop,dimensionErrorEnvelope r k N≤1/2 :=
    (dimensionErrorEnvelope_tendsto_zero r k).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop 1,hs,
    tensorFlatYoungPMF_reciprocal_tail_rate r k hr] with N hN hs ht
  have hm := tensorFlatYoungPMF_mean_inverse_error_split r k N hr hN hs
  have hf := tensorFlatYoungPMF_mean_dimension_error_le r k N hr hN
  calc
    _ ≤ 2*(dimensionMomentRateConstant r k/(N:ℝ))+1/(N:ℝ) := by linarith
    _ = _ := by ring

end Cloning.TensorLie
