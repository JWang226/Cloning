import Cloning.InfinitePowersStormer

/-! Dimension-independent trace-norm continuity of the actual infinite-dimensional root
fidelity. The modulus is derived from the proved Powers–Størmer inequality. -/

namespace Cloning.InfiniteFidelity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace
open InfiniteTraceClass InfiniteTraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma fidelity_continuity_left {A C B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTC : IsTraceClass C) (hTB : IsTraceClass B) :
    |fidelity A B hA hB hTA hTB - fidelity C B hC hB hTC hTB| ≤
      Real.sqrt (traceNorm (A - C) (InfinitePowersStormer.isTraceClass_sub hTA hTC)) *
        Real.sqrt (trace B hTB).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact (fidelity_continuity_left_roots hA hC hB hTA hTC hTB b).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
      (InfinitePowersStormer.sqrt_hilbertSchmidt_square_le_traceNorm hA hC hTA hTC b))
      (Real.sqrt_nonneg _))

lemma fidelity_continuity_right {A B D : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) (hTD : IsTraceClass D) :
    |fidelity A B hA hB hTA hTB - fidelity A D hA hD hTA hTD| ≤
      Real.sqrt (traceNorm (B - D) (InfinitePowersStormer.isTraceClass_sub hTB hTD)) *
        Real.sqrt (trace A hTA).re := by
  rw [fidelity_comm hA hB hTA hTB, fidelity_comm hA hD hTA hTD]
  exact fidelity_continuity_left hB hD hA hTB hTD hTA

lemma fidelity_continuity {A B C D : H →L[ℂ] H}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B)
    (hTC : IsTraceClass C) (hTD : IsTraceClass D) :
    |fidelity A B hA hB hTA hTB - fidelity C D hC hD hTC hTD| ≤
      Real.sqrt (traceNorm (A - C) (InfinitePowersStormer.isTraceClass_sub hTA hTC)) *
        Real.sqrt (trace B hTB).re +
      Real.sqrt (traceNorm (B - D) (InfinitePowersStormer.isTraceClass_sub hTB hTD)) *
        Real.sqrt (trace C hTC).re := by
  exact (abs_sub_le _ (fidelity C B hC hB hTC hTB) _).trans
    (add_le_add (fidelity_continuity_left hA hC hB hTA hTC hTB)
      (fidelity_continuity_right hC hB hD hTC hTB hTD))

/-- The analytic trace distance of two actual density states. -/
def stateTraceDistance (ρ σ : DensityState H) : ℝ :=
  traceNorm (ρ.op - σ.op) (InfinitePowersStormer.isTraceClass_sub ρ.traceClass σ.traceClass)

lemma stateTraceDistance_nonneg (ρ σ : DensityState H) : 0 ≤ stateTraceDistance ρ σ :=
  traceNorm_nonneg _ _

lemma stateTraceDistance_eq_norm (ρ σ : DensityState H) : stateTraceDistance ρ σ =
    ‖TraceClass.ofOperator ρ.op ρ.traceClass - TraceClass.ofOperator σ.op σ.traceClass‖ := rfl

@[simp] lemma stateTraceDistance_self (ρ : DensityState H) : stateTraceDistance ρ ρ = 0 := by
  rw [stateTraceDistance_eq_norm, sub_self, norm_zero]

lemma stateTraceDistance_comm (ρ σ : DensityState H) :
    stateTraceDistance ρ σ = stateTraceDistance σ ρ := by
  simp only [stateTraceDistance_eq_norm, norm_sub_rev]

lemma stateTraceDistance_triangle (ρ σ τ : DensityState H) :
    stateTraceDistance ρ τ ≤ stateTraceDistance ρ σ + stateTraceDistance σ τ := by
  simp only [stateTraceDistance_eq_norm]
  simpa only [dist_eq_norm] using dist_triangle
    (TraceClass.ofOperator ρ.op ρ.traceClass) (TraceClass.ofOperator σ.op σ.traceClass)
    (TraceClass.ofOperator τ.op τ.traceClass)

lemma stateFidelity_continuity (ρ σ ρ' σ' : DensityState H) :
    |stateFidelity ρ σ - stateFidelity ρ' σ'| ≤
      Real.sqrt (stateTraceDistance ρ ρ') + Real.sqrt (stateTraceDistance σ σ') := by
  have h := fidelity_continuity ρ.positive σ.positive ρ'.positive σ'.positive
    ρ.traceClass σ.traceClass ρ'.traceClass σ'.traceClass
  simpa only [σ.trace_one, ρ'.trace_one, Complex.one_re, Real.sqrt_one, mul_one] using h

lemma stateFidelity_continuity_of_traceNorm_le (ρ σ ρ' σ' : DensityState H)
    {ε δ : ℝ} (hε : stateTraceDistance ρ ρ' ≤ ε) (hδ : stateTraceDistance σ σ' ≤ δ) :
    |stateFidelity ρ σ - stateFidelity ρ' σ'| ≤ Real.sqrt ε + Real.sqrt δ :=
  (stateFidelity_continuity ρ σ ρ' σ').trans
    (add_le_add (Real.sqrt_le_sqrt hε) (Real.sqrt_le_sqrt hδ))

lemma traceNorm_sub_eq_trace_sub {A G : H →L[ℂ] H}
    (hTA : IsTraceClass A) (hTG : IsTraceClass G) (hGA : G ≤ A) :
    traceNorm (A - G) (InfinitePowersStormer.isTraceClass_sub hTA hTG) =
      (trace A hTA).re - (trace G hTG).re := by
  have htrace : trace (A - G) (InfinitePowersStormer.isTraceClass_sub hTA hTG) =
      trace A hTA - trace G hTG := by
    have h := trace_add hTA (isTraceClass_smul (-1 : ℂ) hTG)
    rw [trace_smul] at h
    simpa only [neg_one_smul, neg_one_mul, sub_eq_add_neg] using h
  rw [← trace_re_eq_traceNorm (sub_nonneg.mpr hGA), htrace, Complex.sub_re]

/-- Deleting a positive contribution costs at most the square root of its actual trace mass,
times the square root of the target trace. The retained operator need not be normalized. -/
lemma fidelity_deletion_bound {A G B : H →L[ℂ] H}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTG : IsTraceClass G) (hTB : IsTraceClass B) (hGA : G ≤ A) :
    |fidelity A B hA hB hTA hTB - fidelity G B hG hB hTG hTB| ≤
      Real.sqrt ((trace A hTA).re - (trace G hTG).re) * Real.sqrt (trace B hTB).re := by
  simpa only [traceNorm_sub_eq_trace_sub hTA hTG hGA] using
    fidelity_continuity_left hA hG hB hTA hTG hTB

lemma fidelity_deletion_bound_normalized_target {A G : H →L[ℂ] H}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hTA : IsTraceClass A) (hTG : IsTraceClass G)
    (hGA : G ≤ A) (σ : DensityState H) :
    |fidelity A σ.op hA σ.positive hTA σ.traceClass -
      fidelity G σ.op hG σ.positive hTG σ.traceClass| ≤
      Real.sqrt ((trace A hTA).re - (trace G hTG).re) := by
  simpa only [σ.trace_one, Complex.one_re, Real.sqrt_one, mul_one] using
    fidelity_deletion_bound hA hG σ.positive hTA hTG σ.traceClass hGA

end
end Cloning.InfiniteFidelity
