import Cloning.Main
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact one-mode derivative and ratio-wise monotonicity of the cloning values. -/
noncomputable section
open scoped BigOperators Topology
namespace Cloning.ValueComparison
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The exact positive derivative displayed in the manuscript. -/
theorem modeFactor_hasDerivAt {g q : ℝ} (hg : 1 < g) (hq : 0 < q) :
    HasDerivAt (Thermal.modeFactor g)
      ((g-1)^2 / (2*Real.sqrt (q*(g-1+q)) *
        (Real.sqrt (g*(g-1+q))+Real.sqrt q)^2)) q := by
  have hg0 : 0 < g := by linarith
  have hv : 0 < g-1+q := by linarith
  have hrad : 0 < q*(g-1+q) := mul_pos hq hv
  have hden : g+q ≠ 0 := ne_of_gt (add_pos hg0 hq)
  have hd := (((hasDerivAt_const q (Real.sqrt g)).add
    (((hasDerivAt_id q).mul ((hasDerivAt_id q).const_add (g-1))).sqrt hrad.ne')).div
    ((hasDerivAt_id q).const_add g) hden)
  have hr := Real.sq_sqrt hq.le
  have hs := Real.sq_sqrt hv.le
  have ht := Real.sq_sqrt hg0.le
  have hrs : Real.sqrt (q*(g-1+q)) = Real.sqrt q*Real.sqrt (g-1+q) :=
    Real.sqrt_mul hq.le _
  have hts : Real.sqrt (g*(g-1+q)) = Real.sqrt g*Real.sqrt (g-1+q) :=
    Real.sqrt_mul hg0.le _
  have hr0 : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hs0 : Real.sqrt (g-1+q) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hsum : Real.sqrt g*Real.sqrt (g-1+q)+Real.sqrt q ≠ 0 := by positivity
  have htsq : (Real.sqrt g*Real.sqrt (g-1+q))^2=g*(g-1+q) := by
    rw [mul_pow,ht,hs]
  have hrsq : (Real.sqrt q*Real.sqrt (g-1+q))^2=q*(g-1+q) := by
    rw [mul_pow,hr,hs]
  have hnum : (g-1+q+q)*(g+q)-2*Real.sqrt q*Real.sqrt (g-1+q)*
      (Real.sqrt g+Real.sqrt q*Real.sqrt (g-1+q)) =
      (Real.sqrt g*Real.sqrt (g-1+q)-Real.sqrt q)^2 := by
    nlinarith [htsq,hrsq]
  have hprod : (Real.sqrt g*Real.sqrt (g-1+q)-Real.sqrt q)*
      (Real.sqrt g*Real.sqrt (g-1+q)+Real.sqrt q)=(g-1)*(g+q) := by
    nlinarith [htsq]
  convert hd using 1
  simp only [Pi.mul_apply,Pi.add_apply,id_eq,one_mul,mul_one,zero_add]
  rw [hrs,hts]
  field_simp [hr0,hs0,hden,hsum]
  calc
    (g-1)^2*(g+q)^2 = ((Real.sqrt g*Real.sqrt (g-1+q)-Real.sqrt q)*
        (Real.sqrt g*Real.sqrt (g-1+q)+Real.sqrt q))^2 := by rw [hprod]; ring
    _ = _ := by rw [hnum]; ring

theorem modeFactor_deriv_pos {g q : ℝ} (hg : 1 < g) (hq : 0 < q) :
    0 < deriv (Thermal.modeFactor g) q := by
  rw [(modeFactor_hasDerivAt hg hq).deriv]
  have : 0 < g-1+q := by linarith
  have : 0 < g-1 := by linarith
  have : 0 < g := by linarith
  positivity

theorem modeFactor_strictMonoOn {g : ℝ} (hg : 1 < g) :
    StrictMonoOn (Thermal.modeFactor g) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro q hq
    have hc := Thermal.modeFactor_continuousAt (g:=g) (q:=q)
      (by have : 0≤q := hq; linarith)
    exact (hc.comp (by fun_prop : ContinuousAt (fun x : ℝ => (g,x)) q)).continuousWithinAt
  · intro q hq
    rw [interior_Ici] at hq
    exact modeFactor_deriv_pos hg hq

theorem orbitalValue_mono_ratios {d : ℕ} {g : ℝ} (hg : 1 < g)
    (p p' : SimpleSpectrum d) (h : ∀ij, p.ratio ij ≤ p'.ratio ij) :
    orbitalValue g p ≤ orbitalValue g p' := by
  apply Finset.prod_le_prod
  · intro ij _
    exact (Thermal.modeFactor_pos hg (p.ratio_pos ij).le (p.ratio_lt_one ij)).le
  · intro ij _
    exact (modeFactor_strictMonoOn hg).monotoneOn
      (p.ratio_pos ij).le (p'.ratio_pos ij).le (h ij)

theorem orbitalValue_strict_mono_ratios {d : ℕ} {g : ℝ} (hg : 1 < g)
    (p p' : SimpleSpectrum d) (h : ∀ij, p.ratio ij ≤ p'.ratio ij)
    (hs : ∃ij, p.ratio ij < p'.ratio ij) : orbitalValue g p < orbitalValue g p' := by
  apply Finset.prod_lt_prod
  · intro ij _
    exact Thermal.modeFactor_pos hg (p.ratio_pos ij).le (p.ratio_lt_one ij)
  · intro ij _
    exact (modeFactor_strictMonoOn hg).monotoneOn
      (p.ratio_pos ij).le (p'.ratio_pos ij).le (h ij)
  · obtain ⟨ij,hij⟩ := hs
    exact ⟨ij,Finset.mem_univ _,modeFactor_strictMonoOn hg
      (p.ratio_pos ij).le (p'.ratio_pos ij).le hij⟩

theorem universalValue_mono_ratios {d : ℕ} {g : ℝ} (hg : 1 < g)
    (p p' : SimpleSpectrum d) (h : ∀ij, p.ratio ij ≤ p'.ratio ij) :
    universalValue g p ≤ universalValue g p' :=
  mul_le_mul_of_nonneg_left (orbitalValue_mono_ratios hg p p' h)
    (classicalValue_pos (by linarith) d).le

theorem universalValue_strict_mono_ratios {d : ℕ} {g : ℝ} (hg : 1 < g)
    (p p' : SimpleSpectrum d) (h : ∀ij, p.ratio ij ≤ p'.ratio ij)
    (hs : ∃ij, p.ratio ij < p'.ratio ij) : universalValue g p < universalValue g p' :=
  mul_lt_mul_of_pos_left (orbitalValue_strict_mono_ratios hg p p' h hs)
    (classicalValue_pos (by linarith) d)

end Cloning.ValueComparison
