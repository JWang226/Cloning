/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in PHYSLIB-LICENSE.txt.
Authors: Tom Ole Diem

Adapted from Physlib commit f6e446ca99fd83b3a60743a61900cb2acb98f531,
PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Banach.lean.
Upstream blob: 5ca39451b4b42bb0b1f76f3204588b67ab3f8745.
Compatibility: Qualifies map application lemmas and uses the older tendsto_finset_sum name; split into space and completeness modules.
-/

import Cloning.InfiniteTraceClass
import Cloning.InfiniteTraceClassIdeal
import Cloning.InfiniteTraceClassNormBounds
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.Normed.Group.Completeness

/-!

# The trace-class Banach space

## i. Overview

The trace-class operators form a Banach space `𝒮₁(H)` under the trace norm. The trace norm dominates
the operator norm, so an absolutely convergent series of trace-class operators converges in operator
norm. Its limit is trace class because the trace norm is lower semicontinuous along such limits,
which gives completeness.

## ii. Key results

- `TraceClass` : the trace-class operators with the trace norm.
- `opNorm_le_traceNorm` : the operator norm is at most the trace norm.
- `isTraceClass_of_tendsto_of_traceNorm_bounded` : an operator-norm limit of trace-class operators
  with bounded trace norms is trace class.
- `TraceClass.instCompleteSpace` : `𝒮₁(H)` is complete.

## iii. Table of contents

- A. Arithmetic closure of `IsTraceClass`
- B. The trace-class submodule and Banach space

-/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology Filter
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Arithmetic closure of `IsTraceClass` -/

lemma isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, b, by simp [CFC.abs_zero]⟩

/-- Trace-class operators are closed under scalar multiplication. -/
lemma isTraceClass_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (c • T) := by
  obtain ⟨w, b, hb⟩ := hT
  refine ⟨w, b, ?_⟩
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T := CFC.abs_smul c T
  have heq : ∀ i : w, (⟪b i, CFC.abs (c • T) (b i)⟫_ℂ).re
      = ‖c‖ * (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
    intro i
    rw [habs, ContinuousLinearMap.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  simpa only [heq] using hb.mul_left ‖c‖

-- Trace class is closed under addition: `isTraceClass_add`, ported into `GeneralProduct.lean`
-- from the polar-decomposition/Hilbert–Schmidt-factorization argument (see module docstring).
-- That theorem already has exactly the signature `IsTraceClass T → IsTraceClass T' →
-- IsTraceClass (T + T')`, so it is used directly (e.g. below, and in `traceClassSubmodule`)
-- rather than restated here.

lemma isTraceClass_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (-T) := by
  have h := isTraceClass_smul (-1 : ℂ) hT
  rwa [neg_one_smul] at h

lemma traceNorm_zero : traceNorm (0 : H →L[ℂ] H) isTraceClass_zero = 0 := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis isTraceClass_zero b]
  simp [CFC.abs_zero]

/-- The trace norm is absolutely homogeneous: `‖c • T‖₁ = ‖c‖ ‖T‖₁`. -/
lemma traceNorm_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    traceNorm (c • T) (isTraceClass_smul c hT) = ‖c‖ * traceNorm T hT := by
  set w₀ : Set H := hT.choose with hw₀
  set b₀ : HilbertBasis w₀ ℂ H := hT.choose_spec.choose with hb₀def
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T := CFC.abs_smul c T
  have heq : ∀ i : w₀, (⟪b₀ i, CFC.abs (c • T) (b₀ i)⟫_ℂ).re
      = ‖c‖ * (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := by
    intro i
    rw [habs, ContinuousLinearMap.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  rw [traceNorm_eq_of_hilbertBasis (isTraceClass_smul c hT) b₀]
  calc ∑' i : w₀, (⟪b₀ i, CFC.abs (c • T) (b₀ i)⟫_ℂ).re
      = ∑' i : w₀, ‖c‖ * (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := tsum_congr heq
    _ = ‖c‖ * ∑' i : w₀, (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := tsum_mul_left
    _ = ‖c‖ * traceNorm T hT := rfl

lemma traceNorm_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) (hnegT : IsTraceClass (-T)) :
    traceNorm (-T) hnegT = traceNorm T hT := by
  have h1 := traceNorm_smul (-1 : ℂ) hT
  have h2 := traceNorm_transport (neg_one_smul ℂ T) (isTraceClass_smul (-1) hT)
  calc
    traceNorm (-T) hnegT =
        traceNorm (-T) (neg_one_smul ℂ T ▸ isTraceClass_smul (-1) hT) := traceNorm_congr
    _ = traceNorm ((-1 : ℂ) • T) (isTraceClass_smul (-1) hT) := h2.symm
    _ = ‖(-1 : ℂ)‖ * traceNorm T hT := h1
    _ = traceNorm T hT := by norm_num

-- The trace norm is subadditive, `‖T + T'‖₁ ≤ ‖T‖₁ + ‖T'‖₁`: `traceNorm_add_le`, ported into
-- `IdealNorm.lean` from the duality-bound argument (see module docstring), already has exactly
-- this signature, so it is used directly (e.g. in `traceClassAddGroupNorm` below) rather than
-- restated here.

/-- **The operator norm is at most the trace norm.** With `S = √|T|`, Parseval and Cauchy–Schwarz
give `‖S x‖² ≤ ‖T‖₁ ‖x‖²`, and `‖T‖ = ‖S‖²`. -/
lemma opNorm_le_traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ‖T‖ ≤ traceNorm T hT := by
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
  have hTA : ‖T‖ = ‖A‖ := (CFC.norm_abs).symm
  have hAeq : ‖A‖ = ‖S‖ ^ 2 := by rw [← hSS]; exact hSself.norm_mul_self
  set w₀ : Set H := hT.choose with hw₀
  set b₀ : HilbertBasis w₀ ℂ H := hT.choose_spec.choose with hb₀def
  have hb₀ : Summable (fun i : w₀ => (⟪b₀ i, A (b₀ i)⟫_ℂ).re) := hT.choose_spec.choose_spec
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
  have hpt : ∀ i : w₀, (⟪b₀ i, A (b₀ i)⟫_ℂ).re = ‖S (b₀ i)‖ ^ 2 := by
    intro i
    have hinner : ⟪b₀ i, A (b₀ i)⟫_ℂ = ⟪S (b₀ i), S (b₀ i)⟫_ℂ := by
      rw [← hSS]
      show ⟪b₀ i, (S * S) (b₀ i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b₀ i)) (b₀ i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]; norm_cast
  have hSum : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := hb₀.congr hpt
  have htrEq : traceNorm T hT = ∑' i : w₀, ‖S (b₀ i)‖ ^ 2 := tsum_congr hpt
  have htrNonneg : 0 ≤ traceNorm T hT := traceNorm_nonneg T hT
  have hbound : ∀ x : H, ‖S x‖ ^ 2 ≤ traceNorm T hT * ‖x‖ ^ 2 := by
    intro x
    have hpar : HasSum (fun i : w₀ => ‖⟪b₀ i, S x⟫_ℂ‖ ^ 2) (‖S x‖ ^ 2) :=
      hasSum_norm_sq_inner_basis b₀ (S x)
    have heq2 : ∀ i : w₀, ⟪b₀ i, S x⟫_ℂ = ⟪S (b₀ i), x⟫_ℂ := fun i => by
      have h := ContinuousLinearMap.adjoint_inner_left S x (b₀ i)
      rw [hSstar] at h
      exact h.symm
    have hpar' : HasSum (fun i : w₀ => ‖⟪S (b₀ i), x⟫_ℂ‖ ^ 2) (‖S x‖ ^ 2) := by
      simpa [heq2] using hpar
    have hCS : ∀ i : w₀, ‖⟪S (b₀ i), x⟫_ℂ‖ ^ 2 ≤ ‖S (b₀ i)‖ ^ 2 * ‖x‖ ^ 2 := fun i => by
      have h : ‖⟪S (b₀ i), x⟫_ℂ‖ ≤ ‖S (b₀ i)‖ * ‖x‖ := norm_inner_le_norm _ _
      calc ‖⟪S (b₀ i), x⟫_ℂ‖ ^ 2 ≤ (‖S (b₀ i)‖ * ‖x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖S (b₀ i)‖ ^ 2 * ‖x‖ ^ 2 := by ring
    have hdom : HasSum (fun i : w₀ => ‖S (b₀ i)‖ ^ 2 * ‖x‖ ^ 2) (traceNorm T hT * ‖x‖ ^ 2) := by
      rw [htrEq]; exact hSum.hasSum.mul_right (‖x‖ ^ 2)
    exact hasSum_le hCS hpar' hdom
  have hboundNorm : ∀ x : H, ‖S x‖ ≤ Real.sqrt (traceNorm T hT) * ‖x‖ := by
    intro x
    have h1 : ‖S x‖ ^ 2 ≤ traceNorm T hT * ‖x‖ ^ 2 := hbound x
    have h2 : Real.sqrt (‖S x‖ ^ 2) ≤ Real.sqrt (traceNorm T hT * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul htrNonneg,
      Real.sqrt_sq (norm_nonneg _)] at h2
  have hSnorm_le : ‖S‖ ≤ Real.sqrt (traceNorm T hT) :=
    S.opNorm_le_bound (Real.sqrt_nonneg _) hboundNorm
  have hSsq_le : ‖S‖ ^ 2 ≤ traceNorm T hT := by
    have h := pow_le_pow_left₀ (norm_nonneg S) hSnorm_le 2
    rwa [Real.sq_sqrt htrNonneg] at h
  rw [hTA, hAeq]
  exact hSsq_le

/-! ## B. The trace-class submodule and Banach space -/

/-- The trace-class operators, as a submodule of the bounded operators. -/
def traceClassSubmodule (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  zero_mem' := isTraceClass_zero
  add_mem' ha hb := isTraceClass_add ha hb
  smul_mem' c _ ha := isTraceClass_smul c ha

/-- **The trace-class Banach space `𝒮₁(H)`**, normed by the trace norm. It is a `def` so that the
operator norm inherited from the ambient submodule is not found as an instance. -/
def TraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Type _ :=
  traceClassSubmodule H

end
end Cloning.InfiniteTraceClass
