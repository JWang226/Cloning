import Cloning.InfiniteFidelityRegularized

/-! The literal finite inverse-moment hypothesis of the manuscript: a finite
right limit of the bounded regularized inverse moments. No separate uniform
bound or monotonicity hypothesis on those moments is required. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open Filter
namespace Cloning.InfiniteFidelity
open InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weighted root fidelity for arbitrary positive trace-class operators,
with the inverse trace defined by its finite right limit at zero. -/
theorem fidelity_sq_le_of_regularized_inverse_limit {A B W : H→L[ℂ] H}
    (hA : 0≤A) (hB : 0≤B) (hW : 0≤W)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) {M : ℝ}
    (hInv : Tendsto (fun ε : ℝ=>
      (trace (B*CFC.rpow (regularizedWeight W ε) (-1))
        (isTraceClass_mul_mul (A:=1)
          (B:=CFC.rpow (regularizedWeight W ε) (-1)) hTB)).re)
      (𝓝[>] (0:ℝ)) (𝓝 M)) :
    fidelity A B hA hB hTA hTB^2≤
      (trace (A*W) (isTraceClass_mul_mul (A:=1) (B:=W) hTA)).re*M := by
  have hid : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have htrace : Tendsto (fun ε : ℝ=>
      (trace (A*regularizedWeight W ε)
        (isTraceClass_mul_mul (A:=1) (B:=regularizedWeight W ε) hTA)).re)
      (𝓝[>] (0:ℝ))
      (𝓝 ((trace (A*W) (isTraceClass_mul_mul (A:=1) (B:=W) hTA)).re)) := by
    have h := (tendsto_const_nhds (x :=
      (trace (A*W) (isTraceClass_mul_mul (A:=1) (B:=W) hTA)).re)).add
      (hid.mul_const (trace A hTA).re)
    simp only [zero_mul,add_zero] at h
    convert h using 1
    ext ε
    rw [trace_regularizedWeight hTA ε]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (htrace.mul hInv)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact fidelity_sq_le_positive_weight hA hB hTA hTB
    (regularizedWeight_strictlyPositive hW hε)

end Cloning.InfiniteFidelity
