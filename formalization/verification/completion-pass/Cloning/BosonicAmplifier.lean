import Cloning.CoherentCoefficients
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# One-mode quantum-limited amplifier coefficients and Stinespring isometry

For `0 ≤ q < 1`, the gain is `1/(1-q)`. An input number vector `|n⟩`
is mapped to a coherent superposition of the pairs `|n+k,k⟩` with squared
amplitudes `choose(n+k,n) (1-q)^(n+1) q^k`. The negative-binomial
normalization and the orthogonality of these columns are proved here.
-/

noncomputable section
open scoped InnerProductSpace BigOperators Topology

namespace Cloning.BosonicAmplifier

/-- The actual one-mode Fock coefficient Hilbert space. -/
abbrev Fock := lp (fun _ : ℕ => ℂ) 2

/-- The canonical photon-number Hilbert basis. -/
def numberBasis : HilbertBasis ℕ ℂ Fock := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fock)

@[simp] theorem numberBasis_eq_single (n : ℕ) : numberBasis n = lp.single 2 n 1 :=
  (numberBasis.repr_symm_single n).symm

/-- Signal and environment photon-number coefficients. -/
abbrev TwoModeFock := lp (fun _ : ℕ × ℕ => ℂ) 2

/-- Squared amplifier amplitude at input number `n` and created-pair number `k`. -/
def weight (q : ℝ) (n k : ℕ) : ℝ :=
  ((n + k).choose n : ℝ) * (1 - q) ^ (n + 1) * q ^ k

theorem weight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n k : ℕ) :
    0 ≤ weight q n k := by
  have hq : 0 ≤ 1 - q := sub_nonneg.mpr hq1.le
  unfold weight
  positivity

/-- Exact negative-binomial normalization, including zero gain-noise. -/
theorem weight_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    HasSum (weight q n) 1 := by
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one n hq).mul_left
    ((1 - q) ^ (n + 1))
  have hn : (1 - q) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  convert hs using 1
  · ext k
    simp only [weight, Nat.add_comm]
    ring
  · field_simp

theorem weight_tsum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑' k, weight q n k = 1 := (weight_hasSum hq0 hq1 n).tsum_eq

/-- The two-mode joint law of one amplifier column. -/
def columnWeight (q : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 = n + p.2 then weight q n p.2 else 0

theorem columnWeight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) (p : ℕ × ℕ) : 0 ≤ columnWeight q n p := by
  unfold columnWeight
  split_ifs
  · exact weight_nonneg hq0 hq1 _ _
  · exact le_rfl

theorem columnWeight_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    HasSum (columnWeight q n) 1 := by
  let e : ℕ → ℕ × ℕ := fun k => (n + k, k)
  have he : Function.Injective e := fun i j hij => congrArg Prod.snd hij
  have hzero : ∀ p ∉ Set.range e, columnWeight q n p = 0 := by
    intro p hp
    unfold columnWeight
    split_ifs with h
    · exact False.elim (hp ⟨p.2, Prod.ext h.symm rfl⟩)
    · rfl
  apply (he.hasSum_iff hzero).mp
  simpa only [Function.comp_def, e, columnWeight, if_pos rfl] using weight_hasSum hq0 hq1 n

/-- The actual two-mode amplifier output vector for a number input. -/
def column (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) : TwoModeFock :=
  Cloning.CoherentCoefficients.amplitudeVector (columnWeight q n)
    (columnWeight_nonneg hq0 hq1 n) (columnWeight_hasSum hq0 hq1 n)

theorem column_apply (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) (p : ℕ × ℕ) :
    column q hq0 hq1 n p =
      if p.1 = n + p.2 then (Real.sqrt (weight q n p.2) : ℂ) else 0 := by
  simp only [column, Cloning.CoherentCoefficients.amplitudeVector_apply, columnWeight]
  split_ifs <;> simp

theorem column_norm (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ‖column q hq0 hq1 n‖ = 1 := Cloning.CoherentCoefficients.amplitudeVector_norm _ _ _

/-- Different input numbers remain orthogonal; coherences are retained. -/
theorem column_orthonormal (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Orthonormal ℂ (column q hq0 hq1) := by
  refine ⟨column_norm q hq0 hq1, ?_⟩
  intro n m hnm
  rw [lp.inner_eq_tsum]
  suffices h : ∀ p : ℕ × ℕ, ⟪column q hq0 hq1 n p, column q hq0 hq1 m p⟫_ℂ = 0 by
    simp only [h, tsum_zero]
  intro p
  rw [column_apply, column_apply]
  split_ifs with hn hm
  · exact False.elim (hnm (Nat.add_right_cancel (hn.symm.trans hm)))
  · simp
  · simp
  · simp

/-- The genuine coherent linear isometric Stinespring map. -/
def isometry (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : Fock →ₗᵢ[ℂ] TwoModeFock :=
  (column_orthonormal q hq0 hq1).orthogonalFamily.linearIsometry

/-- Its number-basis action is the explicit amplifier column. -/
theorem isometry_single (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    isometry q hq0 hq1 (lp.single 2 n 1) = column q hq0 hq1 n := by
  rw [isometry, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

/-- A fixed environment-number slice is square summable. -/
def sliceVector (k : ℕ) (x : TwoModeFock) : Fock := by
  refine ⟨fun m => x (m, k), memℓp_gen ?_⟩
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective
    (fun i j h => congrArg Prod.fst h)

theorem sliceVector_norm_le (k : ℕ) (x : TwoModeFock) : ‖sliceVector k x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num) x]
  exact Summable.tsum_le_tsum_of_inj (fun m : ℕ => (m, k))
    (fun i j h => congrArg Prod.fst h)
    (fun p _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun _ => le_rfl)
    ((lp.memℓp (sliceVector k x)).summable (by norm_num))
    ((lp.memℓp x).summable (by norm_num))

/-- The bounded slice map extracts the `k`th environment coefficient. -/
def slice (k : ℕ) : TwoModeFock →L[ℂ] Fock :=
  LinearMap.mkContinuous
    { toFun := sliceVector k
      map_add' := by intro x y; ext m; rfl
      map_smul' := by intro c x; ext m; rfl }
    1 (fun x => by simpa only [one_mul] using sliceVector_norm_le k x)

@[simp] theorem slice_apply (k : ℕ) (x : TwoModeFock) (m : ℕ) :
    slice k x m = x (m, k) := rfl

/-- Summing the slice probabilities is exactly the two-mode Hilbert norm. -/
theorem slice_norm_sq_hasSum (x : TwoModeFock) :
    HasSum (fun k => ‖slice k x‖ ^ 2) (‖x‖ ^ 2) := by
  have hfull : HasSum (fun p : ℕ × ℕ => ‖x p‖ ^ (2 : ℕ)) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) x
  have hswap : HasSum (fun p : ℕ × ℕ => ‖x (p.2, p.1)‖ ^ (2 : ℕ)) (‖x‖ ^ 2) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hfull
  apply hswap.prod_fiberwise
  intro k
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, slice_apply] using
    lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) (slice k x)

/-- Genuine amplifier Kraus operators, obtained by slicing the isometry. -/
def kraus (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) : Fock →L[ℂ] Fock :=
  (slice k).comp (isometry q hq0 hq1).toContinuousLinearMap

/-- Exact Kraus normalization on every vector, including coherent superpositions. -/
theorem kraus_norm_sq_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fock) :
    HasSum (fun k => ‖kraus q hq0 hq1 k x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [kraus, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map] using slice_norm_sq_hasSum (isometry q hq0 hq1 x)

/-- The Kraus number-state action is the standard photon-creation shift. -/
theorem kraus_single_apply (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (k n m : ℕ) :
    kraus q hq0 hq1 k (lp.single 2 n 1) m =
      if m = n + k then (Real.sqrt (weight q n k) : ℂ) else 0 := by
  simp only [kraus, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    isometry_single, slice_apply, column_apply]

theorem kraus_numberBasis (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (k n : ℕ) :
    kraus q hq0 hq1 k (numberBasis n) =
      (Real.sqrt (weight q n k) : ℂ) • numberBasis (n + k) := by
  ext m
  simp only [numberBasis_eq_single, kraus_single_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : m = n + k <;> simp [h]

/-- An arbitrary input is mapped by summing amplitudes, not input probabilities. -/
theorem isometry_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fock) :
    HasSum (fun n => x n • column q hq0 hq1 n) (isometry q hq0 hq1 x) :=
  (column_orthonormal q hq0 hq1).orthogonalFamily.hasSum_linearIsometry x

/-- The full amplitude formula also holds for coherent superpositions. -/
theorem isometry_apply (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fock) :
    isometry q hq0 hq1 x = ∑' n, x n • column q hq0 hq1 n :=
  (isometry_hasSum q hq0 hq1 x).tsum_eq.symm

end Cloning.BosonicAmplifier
