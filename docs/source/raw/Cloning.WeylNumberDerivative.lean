import Cloning.WeylNumberKernelDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Strong derivatives of actual multimode Weyl orbits on number vectors. -/
noncomputable section
open scoped InnerProductSpace Topology BigOperators
open MeasureTheory
namespace Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- The literal finite ladder sum on a number state. -/
def numberLadder (a : Fin d → ℂ) (k : Fin d → ℕ) : Fock d :=
  ∑ i, ((a i * (Real.sqrt (k i+1 : ℝ) : ℂ)) •
      numberBasis d (Function.update k i (k i+1)) -
    (starRingEnd ℂ (a i) * (Real.sqrt (k i : ℝ) : ℂ)) •
      numberBasis d (Function.update k i (k i-1)))

theorem prod_numberKernel_update (a z : Fin d → ℂ) (k : Fin d → ℕ)
    (i : Fin d) (l : ℕ) :
    (∏ j, numberKernel (a j) (z j) (Function.update k i l j)) =
      (∏ j ∈ Finset.univ.erase i, numberKernel (a j) (z j) (k j)) *
        numberKernel (a i) (z i) l := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem inner_coherent_displacement_number_hasDerivAt
    (a z : Fin d → ℂ) (k : Fin d → ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪coherentVector z, displacement (s • a) (numberBasis d k)⟫_ℂ)
      ⟪coherentVector z, displacement (t • a) (numberLadder a k)⟫_ℂ t := by
  simp_rw [inner_coherent_displacement_number]
  have h := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (fun i _ => numberKernel_ray_hasDerivAt (a i) (z i) (k i) t)
  convert h using 1
  simp only [numberLadder, map_sum, map_sub, map_smul, inner_sum, inner_sub_right,
    inner_smul_right, inner_coherent_displacement_number, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [prod_numberKernel_update, prod_numberKernel_update]
  simp only [Pi.smul_apply]
  ring

/-- A continuous vector-valued derivative is determined by the total coherent
family. Scalar FTC gives the vector integral, so no weak/strong derivative
identification or unbounded-generator domain is assumed. -/
theorem hasDerivAt_of_coherent_inner
    (f g : ℝ → Fock d) (hg : Continuous g)
    (h : ∀ z t, HasDerivAt (fun s => ⟪coherentVector z, f s⟫_ℂ)
      ⟪coherentVector z, g t⟫_ℂ t) (t : ℝ) : HasDerivAt f (g t) t := by
  have he (u : ℝ) : f u = f 0 + ∫ s in (0 : ℝ)..u, g s := by
    apply sub_eq_zero.mp
    apply coherentVector_total
    intro z
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => h z s) ((continuous_const.inner hg).intervalIntegrable 0 u)
    have hc := (innerSL ℂ (coherentVector z)).intervalIntegral_comp_comm (μ := volume)
      (hg.intervalIntegrable 0 u)
    change (∫ s in (0 : ℝ)..u, ⟪coherentVector z, g s⟫_ℂ) =
      ⟪coherentVector z, ∫ s in (0 : ℝ)..u, g s⟫_ℂ at hc
    rw [hc] at hi
    simp only [inner_sub_right, inner_add_right]
    rw [hi]
    ring
  have hi := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  convert (hasDerivAt_const t (f 0)).add hi using 1
  · exact funext he
  · simp

theorem displacement_number_hasDerivAt (a : Fin d → ℂ) (k : Fin d → ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => displacement (s • a) (numberBasis d k))
      (displacement (t • a) (numberLadder a k)) t := by
  apply hasDerivAt_of_coherent_inner _ (fun s : ℝ => displacement (s • a) (numberLadder a k))
  · exact (continuous_displacement (numberLadder a k)).comp
      (continuous_id.smul continuous_const)
  · exact fun z t => inner_coherent_displacement_number_hasDerivAt a z k t

end Cloning.MultimodeCoherent
