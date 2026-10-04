import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-! Local scalar Taylor estimates with the precise next-order remainder. -/
noncomputable section
open scoped Topology
open Filter Set Asymptotics
namespace Cloning.ScalarTaylor
set_option backward.isDefEq.respectTransparency false
variable {f : ℝ → ℝ} {a : ℝ}

theorem local_taylor_isLittleO (n : ℕ) (hf : ContDiffAt ℝ n f a) :
    (fun x => f x - taylorWithinEval f n univ a x) =o[𝓝 a]
      (fun x => (x-a)^n) := by
  have hf' : ContDiffWithinAt ℝ n f univ a := hf.contDiffWithinAt
  obtain ⟨u,hu,hau,hfu⟩ := hf'.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ a), univ_inter] at hfu
  obtain ⟨l,r,ham,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hau)
  have h := taylor_isLittleO (convex_Ioo l r) ham (hfu.mono hsub)
  rw [nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds ham.1 ham.2)] at h
  have he (x : ℝ) : taylorWithinEval f n (Ioo l r) a x =
      taylorWithinEval f n univ a x := by
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv isOpen_Ioo.uniqueDiffOn
      (hf.of_le (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk))) ham]
  simpa only [he] using h

theorem local_taylor_isBigO (n : ℕ) (hf : ContDiffAt ℝ (n+1) f a) :
    (fun x => f x - taylorWithinEval f n univ a x) =O[𝓝 a]
      (fun x => (x-a)^(n+1)) := by
  have h := (local_taylor_isLittleO (n+1) hf).isBigO
  have ht := isBigO_const_mul_self
    (((((n+1 : ℕ) : ℝ) * n.factorial)⁻¹) * iteratedDeriv (n+1) f a)
    (fun x : ℝ => (x-a)^(n+1)) (𝓝 a)
  convert h.add ht using 1
  ext x
  simp only [taylorWithinEval_succ, iteratedDerivWithin_univ, smul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  ring

/-- The usual second-order expansion, with a cubic big-O error. -/
theorem quadratic_remainder (hf : ContDiffAt ℝ 3 f 0) :
    (fun x => f x - (f 0 + deriv f 0*x + deriv (deriv f) 0/2*x^2))
      =O[𝓝 (0:ℝ)] (fun x => x^3) := by
  have h := local_taylor_isBigO 2 hf
  convert h using 1
  · ext x
    simp only [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_univ, iteratedDeriv_one, iteratedDeriv_succ,
      smul_eq_mul, sub_zero]
    norm_num
    ring
  · simp

end Cloning.ScalarTaylor
