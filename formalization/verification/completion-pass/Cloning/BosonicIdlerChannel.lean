import Cloning.BosonicAmplifierChannel

/-!
# Vacuum-signal output for an arbitrary idler state

Taking slices in the other output coordinate of the amplifier isometry gives
a genuine complementary channel. For input number `l`, the physical signal
and idler pair is `|k,k+l⟩`. The channel retains general input coherences;
only its output number diagonal depends solely on the idler number diagonal.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.BosonicAmplifier

open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false

/-- A slice at a fixed output idler number. -/
def idlerSliceVector (m : ℕ) (x : TwoModeFock) : Fock := by
  refine ⟨fun k => x (m, k), memℓp_gen ?_⟩
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective
    (fun i j h => congrArg Prod.snd h)

theorem idlerSliceVector_norm_le (m : ℕ) (x : TwoModeFock) :
    ‖idlerSliceVector m x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num) x]
  exact Summable.tsum_le_tsum_of_inj (fun k : ℕ => (m, k))
    (fun i j h => congrArg Prod.snd h)
    (fun p _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun _ => le_rfl)
    ((lp.memℓp (idlerSliceVector m x)).summable (by norm_num))
    ((lp.memℓp x).summable (by norm_num))

def idlerSlice (m : ℕ) : TwoModeFock →L[ℂ] Fock :=
  LinearMap.mkContinuous
    { toFun := idlerSliceVector m
      map_add' := by intro x y; ext k; rfl
      map_smul' := by intro c x; ext k; rfl }
    1 (fun x => by simpa only [one_mul] using idlerSliceVector_norm_le m x)

@[simp] theorem idlerSlice_apply (m : ℕ) (x : TwoModeFock) (k : ℕ) :
    idlerSlice m x k = x (m, k) := rfl

theorem idlerSlice_norm_sq_hasSum (x : TwoModeFock) :
    HasSum (fun m => ‖idlerSlice m x‖ ^ 2) (‖x‖ ^ 2) := by
  have hfull : HasSum (fun p : ℕ × ℕ => ‖x p‖ ^ (2 : ℕ)) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) x
  apply hfull.prod_fiberwise
  intro m
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, idlerSlice_apply] using
    lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) (idlerSlice m x)

/-- Kraus operators for the vacuum signal with a general idler input. -/
def idlerKraus (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) : Fock →L[ℂ] Fock :=
  (idlerSlice m).comp (isometry q hq0 hq1).toContinuousLinearMap

theorem idlerKraus_norm_sq_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fock) :
    HasSum (fun m => ‖idlerKraus q hq0 hq1 m x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [idlerKraus, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map] using
      idlerSlice_norm_sq_hasSum (isometry q hq0 hq1 x)

/-- The complementary output is an actual completely positive trace-preserving map. -/
def idlerChannel (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : QuantumChannel Fock Fock :=
  QuantumChannel.ofKraus (idlerKraus q hq0 hq1) (idlerKraus_norm_sq_hasSum q hq0 hq1)

theorem idlerChannel_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock) :
    HasSum (fun m => krausTerm (idlerKraus q hq0 hq1 m) A)
      ((idlerChannel q hq0 hq1).toLinearMap A) := QuantumChannel.ofKraus_hasSum _ _ A

theorem idlerKraus_numberBasis_apply (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m n k : ℕ) :
    idlerKraus q hq0 hq1 m (numberBasis n) k =
      if m = n + k then (Real.sqrt (weight q n k) : ℂ) else 0 := by
  simp only [numberBasis_eq_single, idlerKraus, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, isometry_single, idlerSlice_apply, column_apply]

theorem inner_numberBasis (n : ℕ) (x : Fock) : ⟪numberBasis n, x⟫_ℂ = x n := by
  rw [numberBasis_eq_single, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

theorem idlerKraus_adjoint_numberBasis_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m k n : ℕ) :
    (star (idlerKraus q hq0 hq1 m) (numberBasis k)) n =
      if m = n + k then (Real.sqrt (weight q n k) : ℂ) else 0 := by
  rw [← inner_numberBasis, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_numberBasis,
    idlerKraus_numberBasis_apply]
  split_ifs <;> simp only [map_zero, Complex.conj_ofReal]

/-- On a fixed output number the adjoint Kraus operator selects one idler number. -/
theorem idlerKraus_adjoint_numberBasis_shift
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (l k : ℕ) :
    star (idlerKraus q hq0 hq1 (l + k)) (numberBasis k) =
      (Real.sqrt (weight q l k) : ℂ) • numberBasis l := by
  ext n
  rw [idlerKraus_adjoint_numberBasis_apply]
  simp only [numberBasis_eq_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, Nat.add_right_cancel_iff, smul_eq_mul]
  by_cases h : n = l
  · subst n; simp
  · have h' : l ≠ n := Ne.symm h
    simp [h, h']

theorem idlerKraus_adjoint_numberBasis_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) {m k : ℕ} (hmk : m < k) :
    star (idlerKraus q hq0 hq1 m) (numberBasis k) = 0 := by
  ext n
  rw [idlerKraus_adjoint_numberBasis_apply]
  have h : m ≠ n + k := by omega
  simp [h]

/-- A fixed output number selects exactly one input diagonal coefficient in each
Kraus summand. No positivity or diagonality of the input is assumed. -/
theorem idlerKraus_diagonal_shift
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock) (l k : ℕ) :
    ⟪numberBasis k, (krausTerm (idlerKraus q hq0 hq1 (l + k)) A).1
      (numberBasis k)⟫_ℂ =
    (weight q l k : ℂ) * ⟪numberBasis l, A.1 (numberBasis l)⟫_ℂ := by
  rw [krausTerm, inner_sandwichCLM, idlerKraus_adjoint_numberBasis_shift,
    map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hs : (Real.sqrt (weight q l k) : ℂ) * (Real.sqrt (weight q l k) : ℂ) =
      (weight q l k : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (weight_nonneg hq0 hq1 l k)
  rw [← mul_assoc, hs]

theorem idlerKraus_diagonal_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock)
    {m k : ℕ} (hmk : m < k) :
    ⟪numberBasis k, (krausTerm (idlerKraus q hq0 hq1 m) A).1
      (numberBasis k)⟫_ℂ = 0 := by
  rw [krausTerm, inner_sandwichCLM,
    idlerKraus_adjoint_numberBasis_zero q hq0 hq1 hmk, inner_zero_left]

/-- Exact output number law for an arbitrary trace-class idler, including all
coherences. The law is derived from the norm-convergent Kraus series. -/
theorem idlerChannel_diagonal_hasSum
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock) (k : ℕ) :
    HasSum (fun l => (weight q l k : ℂ) *
      ⟪numberBasis l, A.1 (numberBasis l)⟫_ℂ)
      ⟪numberBasis k, ((idlerChannel q hq0 hq1).toLinearMap A).1
        (numberBasis k)⟫_ℂ := by
  let f : ℕ → ℂ := fun m => ⟪numberBasis k,
    (krausTerm (idlerKraus q hq0 hq1 m) A).1 (numberBasis k)⟫_ℂ
  have hsum : HasSum f ⟪numberBasis k,
      ((idlerChannel q hq0 hq1).toLinearMap A).1 (numberBasis k)⟫_ℂ :=
    (idlerChannel_hasSum q hq0 hq1 A).mapL
      (traceClassMatrixCoefficient (numberBasis k) (numberBasis k))
  have he : Function.Injective (fun l : ℕ => l + k) := by
    intro i j hij
    exact Nat.add_right_cancel hij
  have hzero : ∀ m ∉ Set.range (fun l : ℕ => l + k), f m = 0 := by
    intro m hm
    have hmk : m < k := by
      by_contra hn
      exact hm ⟨m - k, Nat.sub_add_cancel (by omega)⟩
    exact idlerKraus_diagonal_zero q hq0 hq1 A hmk
  have h := (he.hasSum_iff hzero).mpr hsum
  simpa only [Function.comp_def, f, idlerKraus_diagonal_shift] using h

/-- Real output number law; the summands are the idler diagonal times the
negative-binomial transition probability. -/
theorem idlerChannel_diagonal_re_hasSum
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock) (k : ℕ) :
    HasSum (fun l => (⟪numberBasis l, A.1 (numberBasis l)⟫_ℂ).re * weight q l k)
      (⟪numberBasis k, ((idlerChannel q hq0 hq1).toLinearMap A).1
        (numberBasis k)⟫_ℂ).re := by
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_comm] using
    Complex.hasSum_re (idlerChannel_diagonal_hasSum q hq0 hq1 A k)

theorem idlerChannel_diagonal_re
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock) (k : ℕ) :
    (⟪numberBasis k, ((idlerChannel q hq0 hq1).toLinearMap A).1
        (numberBasis k)⟫_ℂ).re =
      ∑' l, (⟪numberBasis l, A.1 (numberBasis l)⟫_ℂ).re * weight q l k :=
  (idlerChannel_diagonal_re_hasSum q hq0 hq1 A k).tsum_eq.symm

end Cloning.BosonicAmplifier
