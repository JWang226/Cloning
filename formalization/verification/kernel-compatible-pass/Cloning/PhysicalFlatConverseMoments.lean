import Cloning.TensorFlatProjectorMoments
import Cloning.YoungFlatFidelity

/-! The exact physical dimension moments give the limiting finite-sample
rank-flat converse bound. No moment convergence is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.PhysicalFlatConverse
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungDimensionRatio
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def flatConverseBound (r k : ℕ) (hr : 0 < r) (n m : ℕ) : ℝ :=
  Real.sqrt ((∑ μ : Shape r n, (tensorFlatYoungPMF n r hr μ).toReal *
    dimensionRatio r k (fun a => ((μ a).val : ℝ))) *
    ∑ μ : Shape r m, (tensorFlatYoungPMF m r hr μ).toReal *
      (dimensionRatio r k (fun a => ((μ a).val : ℝ)))⁻¹)

theorem flatConverseBound_factorization (r k : ℕ) (hr : 0 < r) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    flatConverseBound r k hr n m =
      Real.sqrt (((n : ℝ)/(m : ℝ))^(r*k) *
        (∑ μ, (tensorFlatYoungPMF n r hr μ).toReal * normalizedDimension r k n μ) *
        (∑ μ, (tensorFlatYoungPMF m r hr μ).toReal * inverseNormalizedDimension r k m μ)) := by
  let A := ∑ μ, (tensorFlatYoungPMF n r hr μ).toReal * normalizedDimension r k n μ
  let B := ∑ μ, (tensorFlatYoungPMF m r hr μ).toReal * inverseNormalizedDimension r k m μ
  let c := leadingConstant r k
  have hc : leadingConstant r k ≠ 0 := (leadingConstant_pos r k hr).ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hA : (∑ μ : Shape r n, (tensorFlatYoungPMF n r hr μ).toReal *
      dimensionRatio r k (fun a => ((μ a).val : ℝ))) = c*(n:ℝ)^(r*k)*A := by
    simp only [A,normalizedDimension,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    dsimp only [c,shapeRows]
    field_simp [hc,hn']
    <;> ring
    all_goals rfl
  have hB : (∑ μ : Shape r m, (tensorFlatYoungPMF m r hr μ).toReal *
      (dimensionRatio r k (fun a => ((μ a).val : ℝ)))⁻¹) = B/(c*(m:ℝ)^(r*k)) := by
    simp only [B,inverseNormalizedDimension,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro μ _
    dsimp only [c,shapeRows]
    field_simp [hc,hm']
    <;> ring
    all_goals rfl
  unfold flatConverseBound
  rw [hA,hB]
  congr 1
  change c*(n:ℝ)^(r*k)*A*(B/(c*(m:ℝ)^(r*k))) = ((n:ℝ)/(m:ℝ))^(r*k)*A*B
  rw [div_pow]
  dsimp only [c]
  field_simp [hc,hm']

/-- The actual finite projector upper bound tends to γ^(-r k/2). -/
theorem flatConverseBound_tendsto (r k : ℕ) (hr : 0 < r)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun n => flatConverseBound r k hr n (m n)) atTop
      (𝓝 (γ ^ (-(((r*k : ℕ) : ℝ)/2)))) := by
  have hmom := tensorFlatYoungPMF_dimension_moments r k hr
  have hpow := (hratio.inv₀ hγ.ne').pow (r*k)
  simp only [inv_div] at hpow
  have hall := ((hpow.mul hmom.1).mul (hmom.2.comp hm)).sqrt
  simp only [mul_one,Cloning.YoungFlat.sqrt_inv_nat_pow γ hγ (r*k)] at hall
  apply hall.congr'
  filter_upwards [eventually_gt_atTop 0,hm.eventually (eventually_gt_atTop 0)] with n hn hmn
  exact (flatConverseBound_factorization r k hr n (m n) hn hmn).symm

end Cloning.PhysicalFlatConverse
