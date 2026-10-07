import Cloning.YoungFlatFidelityBounds
import Cloning.TensorFlatProjectorMoments
import Cloning.TensorCloningChannel

/-! The exact-marginal flat coupling attains the crossing-dimension fidelity limit. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungFlat
open Cloning.TensorLie Cloning.TensorCloning Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def coupledFlatFidelity (r k n m : ℕ) (J : PMF (Shape r n × Shape r m)) : ℝ :=
  ∑ z, (J z).toReal *
    (if PartitionCompatible (fun i ↦ (z.1 i).val) (fun i ↦ (z.2 i).val) then
      Real.sqrt (dimensionRatio r k (shapeRows z.1)/dimensionRatio r k (shapeRows z.2)) else 0)

def incompatibleMass (r n m : ℕ) (J : PMF (Shape r n × Shape r m)) : ℝ :=
  ∑ z, if PartitionCompatible (fun i ↦ (z.1 i).val) (fun i ↦ (z.2 i).val) then 0 else (J z).toReal

theorem dimension_fidelity_factorization (r k n m : ℕ) (hr : 0<r) (hn : 0<n) (hm : 0<m)
    (μ : Shape r n) (ν : Shape r m) :
    Real.sqrt (dimensionRatio r k (shapeRows μ)/dimensionRatio r k (shapeRows ν)) =
      Real.sqrt (((n : ℝ)/(m : ℝ))^(r*k)) *
        Real.sqrt (normalizedDimension r k n μ*inverseNormalizedDimension r k m ν) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hc0 := (leadingConstant_pos r k hr).ne'
  have hd0 := (dimensionRatio_pos r k (shapeRows ν) (shapeRows_nonneg ν)).ne'
  have he : dimensionRatio r k (shapeRows μ)/dimensionRatio r k (shapeRows ν) =
      (((n : ℝ)/(m : ℝ))^(r*k))*(normalizedDimension r k n μ*inverseNormalizedDimension r k m ν) := by
    unfold normalizedDimension inverseNormalizedDimension
    rw [div_pow]
    field_simp
  rw [he, Real.sqrt_mul (by positivity)]

theorem coupledFlatFidelity_error_le (r k n m : ℕ) (hr : 0<r) (hn : 0<n) (hm : 0<m)
    (J : PMF (Shape r n × Shape r m))
    (hfst : J.map Prod.fst=tensorFlatYoungPMF n r hr)
    (hsnd : J.map Prod.snd=tensorFlatYoungPMF m r hr) :
    |coupledFlatFidelity r k n m J-Real.sqrt (((n : ℝ)/(m : ℝ))^(r*k))| ≤
      Real.sqrt (((n : ℝ)/(m : ℝ))^(r*k)) *
        (Real.sqrt ((dimensionUniformBound r k+1)*
          (∑ ν, (tensorFlatYoungPMF m r hr ν).toReal*|inverseNormalizedDimension r k m ν-1|)+
          (∑ μ, (tensorFlatYoungPMF n r hr μ).toReal*|normalizedDimension r k n μ-1|))+
          incompatibleMass r n m J) := by
  have hA μ : 0 ≤ normalizedDimension r k n μ := by
    unfold normalizedDimension
    exact div_nonneg (dimensionRatio_pos r k _ (shapeRows_nonneg μ)).le
      (mul_nonneg (leadingConstant_pos r k hr).le (pow_nonneg (Nat.cast_nonneg n) _))
  have hB ν : 0 ≤ inverseNormalizedDimension r k m ν := by
    unfold inverseNormalizedDimension
    exact div_nonneg (mul_nonneg (leadingConstant_pos r k hr).le (pow_nonneg (Nat.cast_nonneg m) _))
      (dimensionRatio_pos r k _ (shapeRows_nonneg ν)).le
  have hAC μ : normalizedDimension r k n μ ≤ dimensionUniformBound r k+1 := by
    have hh := (abs_le.mp (normalizedDimension_global_error r k n hr hn μ)).2
    linarith
  have hmass : (∑ z, (J z).toReal)=1 := by
    rw [← ENNReal.toReal_sum (fun z _ ↦ PMF.apply_ne_top J z), (show (∑ z, J z)=1 from by simpa only [tsum_fintype] using J.tsum_coe), ENNReal.toReal_one]
  have hAmean : (∑ z, (J z).toReal*|normalizedDimension r k n z.1-1|) =
      ∑ μ, (tensorFlatYoungPMF n r hr μ).toReal*|normalizedDimension r k n μ-1| := by
    rw [pmf_sum_map J Prod.fst (fun μ ↦ |normalizedDimension r k n μ-1|), hfst]
  have hBmean : (∑ z, (J z).toReal*|inverseNormalizedDimension r k m z.2-1|) =
      ∑ ν, (tensorFlatYoungPMF m r hr ν).toReal*|inverseNormalizedDimension r k m ν-1| := by
    rw [pmf_sum_map J Prod.snd (fun ν ↦ |inverseNormalizedDimension r k m ν-1|), hsnd]
  have hh := weighted_truncated_sqrt_error (fun z ↦ (J z).toReal)
    (fun z ↦ normalizedDimension r k n z.1) (fun z ↦ inverseNormalizedDimension r k m z.2)
    (fun _ ↦ ENNReal.toReal_nonneg) hmass (fun z ↦ hA z.1) (fun z ↦ hB z.2)
    (dimensionUniformBound r k+1) (fun z ↦ hAC z.1)
    (Real.sqrt (((n : ℝ)/(m : ℝ))^(r*k))) (Real.sqrt_nonneg _)
    (fun z ↦ PartitionCompatible (fun i ↦ (z.1 i).val) (fun i ↦ (z.2 i).val))
  rw [hAmean, hBmean] at hh
  simpa only [coupledFlatFidelity, incompatibleMass,
    dimension_fidelity_factorization r k n m hr hn hm] using hh

/-- The fidelity average depends only on exact physical marginals and vanishing
incompatibility; no independence or unproved dimension moment is supplied. -/
theorem coupledFlatFidelity_tendsto (r k : ℕ) (hr : 0<r) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ ↦ (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (J : ∀ N, PMF (Shape r N × Shape r (m N)))
    (hfst : ∀ N, (J N).map Prod.fst=tensorFlatYoungPMF N r hr)
    (hsnd : ∀ N, (J N).map Prod.snd=tensorFlatYoungPMF (m N) r hr)
    (hbad : Tendsto (fun N ↦ incompatibleMass r N (m N) (J N)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ coupledFlatFidelity r k N (m N) (J N)) atTop
      (𝓝 (Real.sqrt ((γ⁻¹)^(r*k)))) := by
  have hq : Tendsto (fun N : ℕ ↦ Real.sqrt (((N : ℝ)/(m N : ℝ))^(r*k)))
      atTop (𝓝 (Real.sqrt ((γ⁻¹)^(r*k)))) := by
    simpa only [inv_div] using ((hratio.inv₀ (by linarith)).pow (r*k)).sqrt
  have he := ((((tensorFlatYoungPMF_mean_inverse_dimension_error r k hr).comp hm).const_mul
    (dimensionUniformBound r k+1)).add (tensorFlatYoungPMF_mean_dimension_error r k hr)).sqrt
  have hbound := hq.mul (he.add hbad)
  simp only [mul_zero, add_zero, Real.sqrt_zero] at hbound
  have hdiff : Tendsto (fun N ↦ coupledFlatFidelity r k N (m N) (J N)-
      Real.sqrt (((N : ℝ)/(m N : ℝ))^(r*k))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
    filter_upwards [eventually_gt_atTop 0, hm.eventually (eventually_gt_atTop 0)] with N hN hmN
    simpa only [Real.norm_eq_abs] using coupledFlatFidelity_error_le r k N (m N) hr hN hmN
      (J N) (hfst N) (hsnd N)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hq

theorem sqrt_inv_nat_pow (γ : ℝ) (hγ : 0<γ) (a : ℕ) :
    Real.sqrt ((γ⁻¹)^a)=γ^(-((a : ℝ)/2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hγ.le),
    ← Real.rpow_neg_one, ← Real.rpow_mul hγ.le]
  congr 1
  ring

theorem coupledFlatFidelity_tendsto_rpow (r k : ℕ) (hr : 0<r) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ ↦ (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (J : ∀ N, PMF (Shape r N × Shape r (m N)))
    (hfst : ∀ N, (J N).map Prod.fst=tensorFlatYoungPMF N r hr)
    (hsnd : ∀ N, (J N).map Prod.snd=tensorFlatYoungPMF (m N) r hr)
    (hbad : Tendsto (fun N ↦ incompatibleMass r N (m N) (J N)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ coupledFlatFidelity r k N (m N) (J N)) atTop
      (𝓝 (γ^(-(((r*k : ℕ) : ℝ)/2)))) := by
  simpa only [sqrt_inv_nat_pow γ (by linarith) (r*k)] using
    coupledFlatFidelity_tendsto r k hr m hm γ hγ hratio J hfst hsnd hbad

end Cloning.YoungFlat
