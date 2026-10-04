import Cloning.CloningValueExpansionThreshold
import Mathlib.Topology.Algebra.Order.Field

/-! The fixed-spectrum quadratic coefficients diverge at every rank boundary.
No limiting value or rate is assumed for the other eigenvalues. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- The largest and smallest eigenvalues form one actual spectral pair. -/
def boundaryPair (d : ℕ) (hd : 2≤d) : PairIndex d :=
  ⟨(⟨0,by omega⟩,⟨d-1,by omega⟩),by change 0<d-1; omega⟩

theorem one_div_dimension_le_largest {d : ℕ} (hd : 0<d) (p : SimpleSpectrum d) :
    1/(d:ℝ)≤p.eigenvalue ⟨0,hd⟩ := by
  have hs : (1:ℝ)≤(d:ℝ)*p.eigenvalue ⟨0,hd⟩ := by
    calc
      1=∑i,p.eigenvalue i := p.normalized.symm
      _≤∑_i : Fin d,p.eigenvalue ⟨0,hd⟩ := Finset.sum_le_sum (fun (i : Fin d) _=>
        p.strictAnti.antitone (show (⟨0,hd⟩ : Fin d) ≤ i from Nat.zero_le i.val))
      _=(d:ℝ)*p.eigenvalue ⟨0,hd⟩ := by simp
  exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr (by nlinarith)

theorem boundaryRatio_le_dimension_mul_smallest {d : ℕ} (hd : 2≤d)
    (p : SimpleSpectrum d) :
    p.ratio (boundaryPair d hd)≤(d:ℝ)*p.eigenvalue ⟨d-1,by omega⟩ := by
  have hl := one_div_dimension_le_largest (by omega : 0<d) p
  have hdim : (0:ℝ)<d := Nat.cast_pos.mpr (by omega)
  have hh : (1:ℝ)≤p.eigenvalue ⟨0,by omega⟩*(d:ℝ) :=
    (div_le_iff₀ hdim).mp hl
  unfold SimpleSpectrum.ratio boundaryPair
  apply (div_le_iff₀ (p.positive _)).mpr
  have hm := mul_le_mul_of_nonneg_left hh (p.positive ⟨d-1,by omega⟩).le
  nlinarith

theorem pairTerm_le_knownCoefficient {d : ℕ} (p : SimpleSpectrum d) (ij : PairIndex d) :
    1/(4*p.ratio ij)≤knownCoefficient p := by
  exact Finset.single_le_sum (fun kl _=>div_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (p.ratio_pos kl).le)) (Finset.mem_univ ij)

theorem knownCoefficient_le_universalCoefficient {d : ℕ} (hd : 1≤d)
    (p : SimpleSpectrum d) : knownCoefficient p≤universalCoefficient p := by
  have hdim : (1:ℝ)≤d := by exact_mod_cast hd
  dsimp only [universalCoefficient]
  linarith

variable {ι : Type*} {l : Filter ι}

theorem boundaryRatio_tendsto_zero {d : ℕ} (hd : 2≤d) (p : ι→SimpleSpectrum d)
    (hsmall : Tendsto (fun n=>(p n).eigenvalue ⟨d-1,by omega⟩) l (𝓝 0)) :
    Tendsto (fun n=>(p n).ratio (boundaryPair d hd)) l (𝓝 0) := by
  have h := hsmall.const_mul (d:ℝ)
  rw [mul_zero] at h
  exact squeeze_zero (fun n=>((p n).ratio_pos _).le)
    (fun n=>boundaryRatio_le_dimension_mul_smallest hd (p n)) h

theorem knownCoefficient_tendsto_atTop_of_smallest {d : ℕ} (hd : 2≤d)
    (p : ι→SimpleSpectrum d)
    (hsmall : Tendsto (fun n=>(p n).eigenvalue ⟨d-1,by omega⟩) l (𝓝 0)) :
    Tendsto (fun n=>knownCoefficient (p n)) l atTop := by
  have hq : Tendsto (fun n=>(p n).ratio (boundaryPair d hd)) l (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨boundaryRatio_tendsto_zero hd p hsmall,
      Eventually.of_forall (fun n=>(p n).ratio_pos _)⟩
  have hi := (tendsto_inv_nhdsGT_zero.comp hq).const_mul_atTop (by norm_num : (0:ℝ)<1/4)
  have hh : Tendsto (fun n=>1/(4*(p n).ratio (boundaryPair d hd))) l atTop := by
    convert hi using 1
    ext n
    simp only [Function.comp_apply]
    ring
  exact tendsto_atTop_mono (fun n=>pairTerm_le_knownCoefficient (p n) _) hh

/-- Any sequence of actual simple spectra approaching rank loss has an
unbounded universal quadratic infidelity coefficient. -/
theorem universalCoefficient_tendsto_atTop_of_smallest {d : ℕ} (hd : 2≤d)
    (p : ι→SimpleSpectrum d)
    (hsmall : Tendsto (fun n=>(p n).eigenvalue ⟨d-1,by omega⟩) l (𝓝 0)) :
    Tendsto (fun n=>universalCoefficient (p n)) l atTop :=
  tendsto_atTop_mono (fun n=>knownCoefficient_le_universalCoefficient (by omega) (p n))
    (knownCoefficient_tendsto_atTop_of_smallest hd p hsmall)

/-- The PCT coefficient diverges at the same boundary, without requiring
any eigenvalue other than the smallest to converge. -/
theorem pctCoefficient_tendsto_atTop_of_smallest {d : ℕ} (hd : 2≤d)
    (p : ι→SimpleSpectrum d)
    (hsmall : Tendsto (fun n=>(p n).eigenvalue ⟨d-1,by omega⟩) l (𝓝 0)) :
    Tendsto (fun n=>pctCoefficient (p n)) l atTop :=
  tendsto_atTop_mono (fun n=>(universalCoefficient_lt_pctCoefficient hd (p n)).le)
    (universalCoefficient_tendsto_atTop_of_smallest hd p hsmall)

end Cloning.ValueExpansion
