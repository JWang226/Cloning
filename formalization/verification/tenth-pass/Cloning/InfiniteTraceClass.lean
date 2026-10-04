/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in PHYSLIB-LICENSE.txt.
Authors: Tom Ole Diem

Adapted from Physlib commit f6e446ca99fd83b3a60743a61900cb2acb98f531,
PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Basic.lean.
The finite-multiplicity section is deliberately omitted. Compatibility edits remove the newer
Idempotent import, retain CompleteSpace for order monotonicity, qualify sub_apply, and
replace module/public declarations with ordinary imports and a namespace. The namespace is Cloning.InfiniteTraceClass. Checked against Lean v4.29.0-rc6
without changing dependencies. Upstream blob: ddccf1580a99e198952628e83c21d21b094f285e.
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection

/-!

# Trace-class operators

## i. Overview

For a bounded operator `T` on a complex Hilbert space, `|T| = √(T⋆T)` is its absolute value. `T` is
trace class when the diagonal sum `∑ᵢ ⟪eᵢ, |T| eᵢ⟫` converges for a Hilbert basis `{eᵢ}`. The sum is
the trace norm `‖T‖₁`, and `Tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` is the trace.

For positive and self-adjoint operators the diagonal sums do not depend on the basis. The proof
writes `⟪eᵢ, S eᵢ⟫ = ‖√S eᵢ‖²`, expands in a second basis by Parseval and exchanges the two
nonnegative sums. In finite dimension the trace agrees with the linear-algebra trace.

This module provides the analytic trace-class predicate and basis-independent trace norm,
and proves basis independence of the trace for positive and self-adjoint operators. It does
not yet provide a Banach-space bundle, general trace linearity, density operators, or
infinite-dimensional fidelity or Gaussian channels. The upstream finite-multiplicity section
is excluded because it needs a newer Mathlib API.

## ii. Key results

- `IsTraceClass` : a bounded operator is trace class.
- `traceNorm`, `trace` : the trace norm and the trace.
- `summable_inner_abs_of_hilbertBasis` : trace class does not depend on the basis.
- `traceNorm_eq_of_hilbertBasis` : the trace norm does not depend on the basis.
- `trace_eq_of_hilbertBasis_of_isSelfAdjoint` : the trace of a self-adjoint trace-class operator
  does not depend on the basis.
- `trace_eq_sum_inner_hilbertBasis_of_finiteDimensional` : in finite dimension the linear-algebra
  trace is the diagonal sum.

## iii. Table of contents

- A. Trace class
  - A.1. Basis independence

-/

namespace Cloning.InfiniteTraceClass

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Trace class -/

/-- **`T` is trace class**: `∑ᵢ ⟪eᵢ, |T| eᵢ⟫` converges for some Hilbert basis `{eᵢ}` of `H`
(`|T| := CFC.abs T`, Mathlib's continuous functional calculus absolute value `√(T⋆T)`). By the
basis-independence theorem below, "some" is equivalent to "every". -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H), Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re)

/-! ### A.1. Basis independence

The proofs use the square root of the functional calculus and Parseval's identity for Hilbert
bases. -/

omit [CompleteSpace H] in
/-- **Parseval's identity**: `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²` for a Hilbert basis `{eᵢ}`. -/
lemma hasSum_norm_sq_inner_basis {w : Set H} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : w, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ = ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h

/-- For self-adjoint `S`, the sum `∑ᵢ ‖S eᵢ‖²` does not depend on the Hilbert basis. -/
lemma hasSum_norm_sq_apply_of_selfAdjoint {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2) (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
      S).symm.trans hS
  have hcol : ∀ j : w', HasSum (fun i : w => F i j) (‖S (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ = ⟪S (c j), b i⟫_ℂ := fun i => by
      have h1 := ContinuousLinearMap.adjoint_inner_left S (b i) (c j)
      rw [hSstar] at h1
      exact h1.symm
    have key : (fun i : w => F i j) = fun i : w => ‖⟪b i, S (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) (S (c j)), RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b (S (c j))
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) = fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j = ∑' j : w', ‖S (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j = ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖S (c j)‖ ^ 2 = ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm w' w) := by
      funext p
      simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable (fun j : w' => ‖S (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := by
      show Summable fun j : w' => ∑' i : w, Function.uncurry G (j, i)
      exact hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' => ‖S (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

/-- **Trace class does not depend on the basis**: the diagonal of `|T|` is summable in every Hilbert
basis. -/
lemma summable_inner_abs_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
  obtain ⟨w₀, b₀, hb₀⟩ := h
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
          S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    have hval : ⟪S (b' i), S (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [this, hval, Complex.ofReal_re]
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    simpa [hpt b₀] using hb₀
  have := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  simpa [hpt b] using this.summable

/-- An operator is trace class iff the diagonal of `|T|` is summable in every Hilbert basis. -/
lemma isTraceClass_iff {T : H →L[ℂ] H} :
    IsTraceClass T ↔
      ∀ (w : Set H) (b : HilbertBasis w ℂ H),
        Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
  constructor
  · intro h w b
    exact summable_inner_abs_of_hilbertBasis h b
  · intro h
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    exact ⟨w, b, h w b⟩

/-- Every operator on a finite-dimensional Hilbert space is trace class. -/
lemma isTraceClass_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    IsTraceClass T := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  refine ⟨w, b, ?_⟩
  apply summable_of_hasFiniteSupport
  exact Set.finite_univ.subset (by intro i hi; trivial)

omit [CompleteSpace H] in
/-- The ordinary finite-dimensional trace is the diagonal sum in any Hilbert basis. -/
lemma trace_eq_sum_inner_hilbertBasis_of_finiteDimensional
    [FiniteDimensional ℂ H] (T : H →L[ℂ] H) {w : Set H} (b : HilbertBasis w ℂ H) :
    LinearMap.trace ℂ H T.toLinearMap = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  rw [tsum_fintype]
  simpa only [HilbertBasis.coe_toOrthonormalBasis, ContinuousLinearMap.coe_coe] using
    LinearMap.trace_eq_sum_inner T.toLinearMap b.toOrthonormalBasis

/-- The trace norm `‖T‖₁ := ∑ᵢ ⟪eᵢ, |T| eᵢ⟫`, computed via a chosen witness Hilbert basis (any
basis gives the same value, by `summable_inner_abs_of_hilbertBasis` — this definition just needs
*a* witness to compute with). -/
def traceNorm (T : H →L[ℂ] H) (h : IsTraceClass T) : ℝ :=
  ∑' i : h.choose, (⟪h.choose_spec.choose i, CFC.abs T (h.choose_spec.choose i)⟫_ℂ).re

/-- The witness proof argument of `traceNorm` is immaterial.  This small lemma is useful when
transporting a trace-class operator through a construction that produces a new proof of the same
proposition. -/
lemma traceNorm_congr {T : H →L[ℂ] H} {h₁ h₂ : IsTraceClass T} :
    traceNorm T h₁ = traceNorm T h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  rw [hh]

/-- **The trace** `Tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` of a trace-class operator, in the basis witnessing that it
is trace class. -/
def trace (T : H →L[ℂ] H) (h : IsTraceClass T) : ℂ :=
  ∑' i : h.choose, ⟪h.choose_spec.choose i, T (h.choose_spec.choose i)⟫_ℂ

/-- The trace does not depend on the proof that the operator is trace class. -/
lemma trace_congr {T : H →L[ℂ] H} {h₁ h₂ : IsTraceClass T} :
    trace T h₁ = trace T h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  rw [hh]

/-- The trace norm is independent of the witness basis used in `IsTraceClass`.  This is the
strong form of `summable_inner_abs_of_hilbertBasis`: the square-root/Parseval argument identifies
the actual sums, not merely their convergence. -/
lemma traceNorm_eq_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    traceNorm T h = ∑' i, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hb₀ : Summable (fun i : w₀ => (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re) :=
    h.choose_spec.choose_spec
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have hinner : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S :=
        (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    apply hb₀.congr
    intro i
    rw [hAdef, hpt]
  have hnorm := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  calc
    traceNorm T h = ∑' i : w₀, (⟪b₀ i, A (b₀ i)⟫_ℂ).re := by
      rfl
    _ = ∑' i : w₀, ‖S (b₀ i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      exact hpt b₀ i
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := hnorm.tsum_eq.symm
    _ = ∑' i : w, (⟪b i, A (b i)⟫_ℂ).re := by
      apply tsum_congr
      intro i
      exact (hpt b i).symm
    _ = ∑' i, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      rfl

omit [CompleteSpace H] in
lemma real_inner_nonneg_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (x : H) :
    0 ≤ (⟪x, T x⟫_ℂ).re := by
  have hpos : T.IsPositive := T.nonneg_iff_isPositive.mp hT
  have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos x
  have heq : (⟪T x, x⟫_ℂ).re = (⟪x, T x⟫_ℂ).re := by
    rw [← inner_conj_symm (T x) x]
    exact Complex.conj_re _
  rw [← heq]
  exact hx.2

/-- The trace norm is nonnegative.  This is exposed separately from its basis-independence result
so norm estimates can use it without unpacking the chosen Hilbert-basis witness. -/
lemma traceNorm_nonneg (T : H →L[ℂ] H) (h : IsTraceClass T) : 0 ≤ traceNorm T h := by
  unfold traceNorm
  exact tsum_nonneg fun i => real_inner_nonneg_of_nonneg (CFC.abs_nonneg T)
    (h.choose_spec.choose i)

lemma real_inner_mono_of_le {P Q : H →L[ℂ] H} (hPQ : P ≤ Q) (x : H) :
    (⟪x, P x⟫_ℂ).re ≤ (⟪x, Q x⟫_ℂ).re := by
  have hdiff : 0 ≤ Q - P := sub_nonneg.mpr hPQ
  have hpos : (Q - P).IsPositive := (Q - P).nonneg_iff_isPositive.mp hdiff
  have hx := (ContinuousLinearMap.isPositive_iff_complex (Q - P)).mp hpos x
  have heq : (⟪(Q - P) x, x⟫_ℂ).re = (⟪x, (Q - P) x⟫_ℂ).re := by
    rw [← inner_conj_symm ((Q - P) x) x]
    exact Complex.conj_re _
  have hx' : 0 ≤ (⟪x, (Q - P) x⟫_ℂ).re := by
    rw [← heq]
    exact hx.2
  simpa [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub] using hx'

lemma isTraceClass_posPart_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) : IsTraceClass T⁺ := by
  obtain ⟨w, b, hb⟩ := h
  refine ⟨w, b, ?_⟩
  rw [CFC.abs_of_nonneg T⁺ (CFC.posPart_nonneg T)]
  apply Summable.of_nonneg_of_le
  · intro i
    exact real_inner_nonneg_of_nonneg (CFC.posPart_nonneg T) (b i)
  · intro i
    have habs : T⁺ + T⁻ = CFC.abs T := CFC.posPart_add_negPart T hT
    have hle : T⁺ ≤ CFC.abs T := by
      rw [← habs]
      exact le_add_of_nonneg_right (CFC.negPart_nonneg T)
    exact real_inner_mono_of_le hle (b i)
  · exact hb

lemma isTraceClass_negPart_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) : IsTraceClass T⁻ := by
  obtain ⟨w, b, hb⟩ := h
  refine ⟨w, b, ?_⟩
  rw [CFC.abs_of_nonneg T⁻ (CFC.negPart_nonneg T)]
  apply Summable.of_nonneg_of_le
  · intro i
    exact real_inner_nonneg_of_nonneg (CFC.negPart_nonneg T) (b i)
  · intro i
    have habs : T⁺ + T⁻ = CFC.abs T := CFC.posPart_add_negPart T hT
    have hle : T⁻ ≤ CFC.abs T := by
      rw [← habs]
      exact le_add_of_nonneg_left (CFC.posPart_nonneg T)
    exact real_inner_mono_of_le hle (b i)
  · exact hb

lemma summable_inner_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (h : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i => ⟪b i, T (b i)⟫_ℂ) := by
  have hr : Summable (fun i : w => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) :=
    summable_inner_abs_of_hilbertBasis h b
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
  have heq (i : w) : ⟪b i, T (b i)⟫_ℂ =
      ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
    rw [habs]
    have hpos : T.IsPositive := T.nonneg_iff_isPositive.mp hT
    have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos (b i)
    have hA : ⟪T (b i), b i⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪T (b i), b i⟫_ℂ).re = (⟪b i, T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (T (b i)) (b i)]
      exact Complex.conj_re _
    have hinner : ⟪b i, T (b i)⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪T (b i), b i⟫_ℂ).re : ℂ) :=
          congrArg (starRingEnd ℂ) hA
        _ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by simp
    exact hinner.trans (congrArg (fun r : ℝ => (r : ℂ)) hre)
  have hs : Summable (fun i : w => ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ)) :=
    Complex.summable_ofReal.mpr hr
  exact hs.congr (fun i => (heq i).symm)

/-!
Basis-independent trace for positive trace-class operators.

For a positive operator the absolute value is the operator itself.  Taking its continuous-
functional-calculus square root turns every diagonal coefficient into a squared norm, so the
Parseval double-sum theorem already proved above gives the same sum in every Hilbert basis.  This
is the positive case needed by density operators and does not use polar decomposition.
-/
lemma trace_eq_of_hilbertBasis_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (h : IsTraceClass T) {w : Set H} (b : HilbertBasis w ℂ H) :
    trace T h = ∑' i, ⟪b i, T (b i)⟫_ℂ := by
  let S : H →L[ℂ] H := CFC.sqrt T
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg T)
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  have hdiag : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      ⟪b' i, T (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
    intro w' b' i
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    have hinner : ⟪b' i, T (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hWdiag : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    have hbase : Summable (fun i : w₀ =>
        (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re) := h.choose_spec.choose_spec
    have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
    apply hbase.congr
    intro i
    rw [habs, hdiag b₀ i]
    rfl
  have hnorm := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hWdiag
  calc
    trace T h = ∑' i : w₀, ⟪b₀ i, T (b₀ i)⟫_ℂ := by
      rfl
    _ = ∑' i : w₀, ((‖S (b₀ i)‖ ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro i
      exact hdiag b₀ i
    _ = ((∑' i : w₀, ‖S (b₀ i)‖ ^ 2 : ℝ) : ℂ) :=
      (Complex.ofReal_tsum (fun i : w₀ => ‖S (b₀ i)‖ ^ 2)).symm
    _ = ((∑' i : w, ‖S (b i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hnorm.tsum_eq]
    _ = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro i
      exact (hdiag b i).symm

/-- Basis-independent trace for self-adjoint trace-class operators.  The proof reduces to the
positive theorem through the continuous-functional-calculus decomposition `T = T⁺ - T⁻`; no
polar decomposition is needed for this self-adjoint case. -/
lemma trace_eq_of_hilbertBasis_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) {w : Set H} (b : HilbertBasis w ℂ H) :
    trace T h = ∑' i, ⟪b i, T (b i)⟫_ℂ := by
  let P : H →L[ℂ] H := T⁺
  let N : H →L[ℂ] H := T⁻
  have hP : IsTraceClass P := isTraceClass_posPart_of_isSelfAdjoint hT h
  have hN : IsTraceClass N := isTraceClass_negPart_of_isSelfAdjoint hT h
  have hPnonneg : 0 ≤ P := CFC.posPart_nonneg T
  have hNnonneg : 0 ≤ N := CFC.negPart_nonneg T
  have hdecomp : P - N = T := CFC.posPart_sub_negPart T hT
  have hPsum : Summable (fun i : w => ⟪b i, P (b i)⟫_ℂ) :=
    summable_inner_of_nonneg hPnonneg hP b
  have hNsum : Summable (fun i : w => ⟪b i, N (b i)⟫_ℂ) :=
    summable_inner_of_nonneg hNnonneg hN b
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hPsum₀ : Summable (fun i : w₀ => ⟪b₀ i, P (b₀ i)⟫_ℂ) :=
    summable_inner_of_nonneg hPnonneg hP b₀
  have hNsum₀ : Summable (fun i : w₀ => ⟪b₀ i, N (b₀ i)⟫_ℂ) :=
    summable_inner_of_nonneg hNnonneg hN b₀
  have htrace_sub : trace T h = trace P hP - trace N hN := by
    calc
      trace T h = ∑' i : w₀, ⟪b₀ i, T (b₀ i)⟫_ℂ := by rfl
      _ = ∑' i : w₀, (⟪b₀ i, P (b₀ i)⟫_ℂ - ⟪b₀ i, N (b₀ i)⟫_ℂ) := by
        apply tsum_congr
        intro i
        rw [← hdecomp]
        simp [ContinuousLinearMap.sub_apply, inner_sub_right]
      _ = (∑' i : w₀, ⟪b₀ i, P (b₀ i)⟫_ℂ) -
          (∑' i : w₀, ⟪b₀ i, N (b₀ i)⟫_ℂ) := hPsum₀.tsum_sub hNsum₀
      _ = trace P hP - trace N hN := by
        rw [trace_eq_of_hilbertBasis_of_nonneg hPnonneg hP b₀,
          trace_eq_of_hilbertBasis_of_nonneg hNnonneg hN b₀]
  calc
    trace T h = trace P hP - trace N hN := htrace_sub
    _ = (∑' i : w, ⟪b i, P (b i)⟫_ℂ) -
        (∑' i : w, ⟪b i, N (b i)⟫_ℂ) := by
      rw [trace_eq_of_hilbertBasis_of_nonneg hPnonneg hP b,
        trace_eq_of_hilbertBasis_of_nonneg hNnonneg hN b]
    _ = ∑' i : w, (⟪b i, P (b i)⟫_ℂ - ⟪b i, N (b i)⟫_ℂ) :=
      (hPsum.tsum_sub hNsum).symm
    _ = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
      apply tsum_congr
      intro i
      rw [← hdecomp]
      simp [ContinuousLinearMap.sub_apply, inner_sub_right]


/-- In finite dimension the analytic trace agrees with the ordinary linear-algebra trace. -/
lemma trace_eq_linearMap_trace_of_finiteDimensional [FiniteDimensional ℂ H]
    (T : H →L[ℂ] H) (h : IsTraceClass T) :
    trace T h = LinearMap.trace ℂ H T.toLinearMap := by
  exact (trace_eq_sum_inner_hilbertBasis_of_finiteDimensional T h.choose_spec.choose).symm

end
end Cloning.InfiniteTraceClass
