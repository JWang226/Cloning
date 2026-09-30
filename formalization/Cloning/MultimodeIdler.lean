import Cloning.BosonicIdlerChannel
import Cloning.BosonicNumberLaw

/-!
# Genuine multimode vacuum-signal/idler channel

The input is the full occupation Hilbert space, not its diagonal subspace.
For every occupation tuple `l`, the isometry has coherent amplitudes
`sqrt (productLaw q l k)` on `|l+k,k⟩`. Slicing the first coordinate gives
an actual CPTP channel whose number diagonal is the negative-binomial mixture
of the input number diagonal, for arbitrary correlated and coherent idlers.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeIdler

open Cloning.InfiniteTraceClass BosonicNumberLaw
set_option backward.isDefEq.respectTransparency false

abbrev Occupation (s : ℕ) := Fin s → ℕ
abbrev Fock (s : ℕ) := lp (fun _ : Occupation s => ℂ) 2
abbrev JointFock (s : ℕ) := lp (fun _ : Occupation s × Occupation s => ℂ) 2

def numberBasis (s : ℕ) : HilbertBasis (Occupation s) ℂ (Fock s) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (Fock s))

@[simp] theorem numberBasis_eq_single {s : ℕ} (n : Occupation s) :
    numberBasis s n = lp.single 2 n 1 := (numberBasis s |>.repr_symm_single n).symm

variable {s : ℕ}

/-- Joint probability support of a fixed idler occupation column. -/
def columnWeight (q : Fin s → ℝ) (l : Occupation s)
    (p : Occupation s × Occupation s) : ℝ :=
  if p.1 = l + p.2 then productLaw q l p.2 else 0

theorem columnWeight_nonneg {q : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (l : Occupation s) (p : Occupation s × Occupation s) :
    0 ≤ columnWeight q l p := by
  unfold columnWeight
  split_ifs
  · exact productLaw_nonneg hq0 hq1 _ _
  · exact le_rfl

theorem columnWeight_hasSum {q : Fin s → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (l : Occupation s) :
    HasSum (columnWeight q l) 1 := by
  let e : Occupation s → Occupation s × Occupation s := fun k => (l + k, k)
  have he : Function.Injective e := fun i j hij => congrArg Prod.snd hij
  have hzero : ∀ p ∉ Set.range e, columnWeight q l p = 0 := by
    intro p hp
    unfold columnWeight
    split_ifs with h
    · exact False.elim (hp ⟨p.2, Prod.ext h.symm rfl⟩)
    · rfl
  apply (he.hasSum_iff hzero).mp
  simpa only [Function.comp_def, e, columnWeight, if_pos rfl] using
    productLaw_hasSum hq0 hq1 l

/-- Coherent multimode output column. -/
def column (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (l : Occupation s) : JointFock s :=
  Cloning.CoherentCoefficients.amplitudeVector (columnWeight q l)
    (columnWeight_nonneg hq0 hq1 l) (columnWeight_hasSum hq0 hq1 l)

theorem column_apply (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (l : Occupation s) (p : Occupation s × Occupation s) :
    column q hq0 hq1 l p =
      if p.1 = l + p.2 then (Real.sqrt (productLaw q l p.2) : ℂ) else 0 := by
  simp only [column, Cloning.CoherentCoefficients.amplitudeVector_apply, columnWeight]
  split_ifs <;> simp

theorem column_norm (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (l : Occupation s) : ‖column q hq0 hq1 l‖ = 1 :=
  Cloning.CoherentCoefficients.amplitudeVector_norm _ _ _

theorem column_orthonormal (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Orthonormal ℂ (column q hq0 hq1) := by
  refine ⟨column_norm q hq0 hq1, ?_⟩
  intro n m hnm
  rw [lp.inner_eq_tsum]
  suffices h : ∀ p : Occupation s × Occupation s,
      ⟪column q hq0 hq1 n p, column q hq0 hq1 m p⟫_ℂ = 0 by
    simp only [h, tsum_zero]
  intro p
  rw [column_apply, column_apply]
  split_ifs with hn hm
  · exact False.elim (hnm (add_right_cancel (hn.symm.trans hm)))
  · simp
  · simp
  · simp

/-- An actual linear isometry, retaining all input coherences. -/
def isometry (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Fock s →ₗᵢ[ℂ] JointFock s :=
  (column_orthonormal q hq0 hq1).orthogonalFamily.linearIsometry

theorem isometry_single (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (l : Occupation s) :
    isometry q hq0 hq1 (lp.single 2 l 1) = column q hq0 hq1 l := by
  rw [isometry, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

theorem isometry_hasSum (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (x : Fock s) :
    HasSum (fun l => x l • column q hq0 hq1 l) (isometry q hq0 hq1 x) :=
  (column_orthonormal q hq0 hq1).orthogonalFamily.hasSum_linearIsometry x

/-- The signal vector at a fixed output idler occupation. -/
def sliceVector (m : Occupation s) (x : JointFock s) : Fock s := by
  refine ⟨fun k => x (m, k), memℓp_gen ?_⟩
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective
    (fun i j h => congrArg Prod.snd h)

theorem sliceVector_norm_le (m : Occupation s) (x : JointFock s) :
    ‖sliceVector m x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num) x]
  exact Summable.tsum_le_tsum_of_inj (fun k : Occupation s => (m, k))
    (fun i j h => congrArg Prod.snd h)
    (fun p _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun _ => le_rfl)
    ((lp.memℓp (sliceVector m x)).summable (by norm_num))
    ((lp.memℓp x).summable (by norm_num))

def slice (m : Occupation s) : JointFock s →L[ℂ] Fock s :=
  LinearMap.mkContinuous
    { toFun := sliceVector m
      map_add' := by intro x y; ext k; rfl
      map_smul' := by intro c x; ext k; rfl }
    1 (fun x => by simpa only [one_mul] using sliceVector_norm_le m x)

@[simp] theorem slice_apply (m : Occupation s) (x : JointFock s) (k : Occupation s) :
    slice m x k = x (m, k) := rfl

theorem slice_norm_sq_hasSum (x : JointFock s) :
    HasSum (fun m => ‖slice m x‖ ^ 2) (‖x‖ ^ 2) := by
  have hfull : HasSum (fun p : Occupation s × Occupation s => ‖x p‖ ^ (2 : ℕ))
      (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) x
  apply hfull.prod_fiberwise
  intro m
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, slice_apply] using
    lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) (slice m x)

/-- Multimode idler Kraus operators obtained by actual Hilbert-space slicing. -/
def kraus (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (m : Occupation s) : Fock s →L[ℂ] Fock s :=
  (slice m).comp (isometry q hq0 hq1).toContinuousLinearMap

theorem kraus_norm_sq_hasSum (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (x : Fock s) :
    HasSum (fun m => ‖kraus q hq0 hq1 m x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [kraus, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map] using
    slice_norm_sq_hasSum (isometry q hq0 hq1 x)

/-- The actual CPTP signal-output map for an arbitrary multimode idler. -/
def channel (q : Fin s → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    QuantumChannel (Fock s) (Fock s) :=
  QuantumChannel.ofKraus (kraus q hq0 hq1) (kraus_norm_sq_hasSum q hq0 hq1)

theorem channel_hasSum (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (A : TraceClass (Fock s)) :
    HasSum (fun m => krausTerm (kraus q hq0 hq1 m) A)
      ((channel q hq0 hq1).toLinearMap A) := QuantumChannel.ofKraus_hasSum _ _ A

theorem kraus_numberBasis_apply (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (m n k : Occupation s) :
    kraus q hq0 hq1 m (numberBasis s n) k =
      if m = n + k then (Real.sqrt (productLaw q n k) : ℂ) else 0 := by
  simp only [numberBasis_eq_single, kraus, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, isometry_single, slice_apply, column_apply]

theorem inner_numberBasis (n : Occupation s) (x : Fock s) :
    ⟪numberBasis s n, x⟫_ℂ = x n := by
  rw [numberBasis_eq_single, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

theorem kraus_adjoint_numberBasis_apply (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (m k n : Occupation s) :
    (star (kraus q hq0 hq1 m) (numberBasis s k)) n =
      if m = n + k then (Real.sqrt (productLaw q n k) : ℂ) else 0 := by
  rw [← inner_numberBasis, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_numberBasis,
    kraus_numberBasis_apply]
  split_ifs <;> simp only [map_zero, Complex.conj_ofReal]

theorem kraus_adjoint_numberBasis_shift (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (l k : Occupation s) :
    star (kraus q hq0 hq1 (l + k)) (numberBasis s k) =
      (Real.sqrt (productLaw q l k) : ℂ) • numberBasis s l := by
  ext n
  rw [kraus_adjoint_numberBasis_apply]
  simp only [numberBasis_eq_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, add_right_cancel_iff, smul_eq_mul]
  by_cases h : n = l
  · subst n; simp
  · have h' : l ≠ n := Ne.symm h
    simp [h, h']

theorem kraus_adjoint_numberBasis_zero (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (m k : Occupation s)
    (hmk : m ∉ Set.range (fun l : Occupation s => l + k)) :
    star (kraus q hq0 hq1 m) (numberBasis s k) = 0 := by
  ext n
  rw [kraus_adjoint_numberBasis_apply]
  have h : m ≠ n + k := fun h => hmk ⟨n, h.symm⟩
  simp [h]

theorem kraus_diagonal_shift (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (A : TraceClass (Fock s)) (l k : Occupation s) :
    ⟪numberBasis s k, (krausTerm (kraus q hq0 hq1 (l + k)) A).1
      (numberBasis s k)⟫_ℂ =
    (productLaw q l k : ℂ) * ⟪numberBasis s l, A.1 (numberBasis s l)⟫_ℂ := by
  rw [krausTerm, inner_sandwichCLM, kraus_adjoint_numberBasis_shift,
    map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hs : (Real.sqrt (productLaw q l k) : ℂ) *
      (Real.sqrt (productLaw q l k) : ℂ) = (productLaw q l k : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (productLaw_nonneg hq0 hq1 l k)
  rw [← mul_assoc, hs]

theorem kraus_diagonal_zero (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (A : TraceClass (Fock s)) (m k : Occupation s)
    (hmk : m ∉ Set.range (fun l : Occupation s => l + k)) :
    ⟪numberBasis s k, (krausTerm (kraus q hq0 hq1 m) A).1
      (numberBasis s k)⟫_ℂ = 0 := by
  rw [krausTerm, inner_sandwichCLM,
    kraus_adjoint_numberBasis_zero q hq0 hq1 m k hmk, inner_zero_left]

/-- Exact complex series for the output diagonal of any trace-class idler. -/
theorem channel_diagonal_hasSum (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (A : TraceClass (Fock s)) (k : Occupation s) :
    HasSum (fun l => (productLaw q l k : ℂ) *
      ⟪numberBasis s l, A.1 (numberBasis s l)⟫_ℂ)
      ⟪numberBasis s k, ((channel q hq0 hq1).toLinearMap A).1
        (numberBasis s k)⟫_ℂ := by
  let f : Occupation s → ℂ := fun m => ⟪numberBasis s k,
    (krausTerm (kraus q hq0 hq1 m) A).1 (numberBasis s k)⟫_ℂ
  have hsum : HasSum f ⟪numberBasis s k,
      ((channel q hq0 hq1).toLinearMap A).1 (numberBasis s k)⟫_ℂ :=
    (channel_hasSum q hq0 hq1 A).mapL
      (traceClassMatrixCoefficient (numberBasis s k) (numberBasis s k))
  have he : Function.Injective (fun l : Occupation s => l + k) := by
    intro i j hij
    exact add_right_cancel hij
  have hzero : ∀ m ∉ Set.range (fun l : Occupation s => l + k), f m = 0 :=
    fun m hm => kraus_diagonal_zero q hq0 hq1 A m k hm
  have h := (he.hasSum_iff hzero).mpr hsum
  simpa only [Function.comp_def, f, kraus_diagonal_shift] using h

theorem channel_diagonal_re_hasSum (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (A : TraceClass (Fock s)) (k : Occupation s) :
    HasSum (fun l => (⟪numberBasis s l, A.1 (numberBasis s l)⟫_ℂ).re * productLaw q l k)
      (⟪numberBasis s k, ((channel q hq0 hq1).toLinearMap A).1
        (numberBasis s k)⟫_ℂ).re := by
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_comm] using
    Complex.hasSum_re (channel_diagonal_hasSum q hq0 hq1 A k)

/-- The full correlated-idler number law. No diagonal-input assumption appears. -/
theorem channel_diagonal_re (q : Fin s → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (A : TraceClass (Fock s)) (k : Occupation s) :
    (⟪numberBasis s k, ((channel q hq0 hq1).toLinearMap A).1
        (numberBasis s k)⟫_ℂ).re =
      mixtureLaw q (fun l => (⟪numberBasis s l, A.1 (numberBasis s l)⟫_ℂ).re) k :=
  (channel_diagonal_re_hasSum q hq0 hq1 A k).tsum_eq.symm

end Cloning.MultimodeIdler
