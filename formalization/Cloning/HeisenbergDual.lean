import Cloning.InfiniteTraceClassPairing
import Cloning.InfiniteCompletelyPositive

/-! The Banach dual of the genuine trace-class space, reconstructed as actual
bounded Hilbert-space operators. This gives the normal Heisenberg adjoint of
an arbitrary bounded trace-class map, with no representation hypothesis. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The rank-one map is bounded in the actual trace norm. -/
def rankOneTraceClass : H →L[ℂ] H →L⋆[ℂ] TraceClass H :=
  LinearMap.mkContinuous₂
    { toFun := fun x =>
        { toFun := fun y => rankOneOperator x y
          map_add' := by
            intro y z
            apply Subtype.ext
            exact (InnerProductSpace.rankOne ℂ x).map_add y z
          map_smul' := by
            intro c y
            apply Subtype.ext
            exact (InnerProductSpace.rankOne ℂ x).map_smulₛₗ c y }
      map_add' := by
        intro x y
        ext z
        apply Subtype.ext
        exact congrArg (fun f => f z) ((InnerProductSpace.rankOne ℂ).map_add x y)
      map_smul' := by
        intro c x
        ext y
        apply Subtype.ext
        exact congrArg (fun f => f y) ((InnerProductSpace.rankOne ℂ).map_smul c x) }
    1 (fun x y => by simpa using (norm_rankOneOperator x y).le)

@[simp] theorem rankOneTraceClass_apply (x y : H) :
    rankOneTraceClass x y = rankOneOperator x y := rfl

/-- A bounded trace-class functional determines a bounded sesquilinear form. -/
def traceClassDualForm (f : TraceClass H →L[ℂ] ℂ) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ H (TraceClass H) ℂ f).comp rankOneTraceClass.flip

/-- Riesz reconstruction of the entire dual of trace class. -/
def traceClassDualOp (f : TraceClass H →L[ℂ] ℂ) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (traceClassDualForm f)).adjoint

@[simp] theorem traceClassDualOp_inner (f : TraceClass H →L[ℂ] ℂ) (x y : H) :
    ⟪y, traceClassDualOp f x⟫_ℂ = f (rankOneOperator x y) := by
  rw [traceClassDualOp, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- Rank-one trace tests recover all operator matrix coefficients. -/
theorem tracePairing_rankOneOperator (x y : H) (A : H →L[ℂ] H) :
    tracePairing (rankOneOperator x y) A = ⟪y, A x⟫_ℂ := by
  change trace (InnerProductSpace.rankOne ℂ x y * A) _ = _
  rw [← trace_mul_cycle (isTraceClass_rankOne x y)]
  change trace (A * InnerProductSpace.rankOne ℂ x y) _ = _
  simpa only [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne] using
    trace_rankOne_general (A x) y

/-- Continuous functionals on trace class agree if they agree on positive
rank-one projectors. The Jordan decomposition supplies all complex inputs. -/
theorem traceClass_functional_ext (f g : TraceClass H →L[ℂ] ℂ)
    (h : ∀ x : H, f (vectorProjector x) = g (vectorProjector x)) : f = g := by
  have hpos (T : TraceClass H) (hT : 0 ≤ T.1) : f T = g T := by
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    have hf := (positive_rankOne_series hT T.2 b).mapL f
    have hg := (positive_rankOne_series hT T.2 b).mapL g
    simp only [h] at hf
    exact hf.unique hg
  have hsa (T : TraceClass H) (hT : IsSelfAdjoint T.1) : f T = g T := by
    rw [← TraceClass.positivePart_sub_negativePart T hT, map_sub, map_sub,
      hpos _ (TraceClass.positivePart_nonneg T hT),
      hpos _ (TraceClass.negativePart_nonneg T hT)]
  ext T
  rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent T,
    map_add, map_add, map_smul, map_smul,
    hsa _ (TraceClass.realComponent_isSelfAdjoint T),
    hsa _ (TraceClass.imaginaryComponent_isSelfAdjoint T)]

/-- Full trace duality, including nonpositive and off-diagonal inputs. -/
theorem tracePairing_traceClassDualOp (f : TraceClass H →L[ℂ] ℂ) (T : TraceClass H) :
    tracePairing T (traceClassDualOp f) = f T := by
  have heq : (ContinuousLinearMap.apply ℂ ℂ (traceClassDualOp f)).comp tracePairingCLM = f := by
    apply traceClass_functional_ext
    intro x
    change tracePairing (rankOneOperator x x) (traceClassDualOp f) = f (rankOneOperator x x)
    rw [tracePairing_rankOneOperator, traceClassDualOp_inner]
  exact congrArg (fun F : TraceClass H →L[ℂ] ℂ => F T) heq

/-- Bounded operators are uniquely determined by their trace-class pairings. -/
theorem tracePairing_separates {A B : H →L[ℂ] H}
    (h : ∀ T : TraceClass H, tracePairing T A = tracePairing T B) : A = B := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simpa only [tracePairing_rankOneOperator] using h (rankOneOperator x y)

/-- The representing operator obeys the exact dual norm bound. -/
theorem norm_traceClassDualOp_le (f : TraceClass H →L[ℂ] ℂ) :
    ‖traceClassDualOp f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hb := f.le_opNorm (rankOneOperator x (traceClassDualOp f x))
  rw [← traceClassDualOp_inner, inner_self_eq_norm_sq_to_K] at hb
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm, norm_rankOneOperator] at hb
  by_cases hz : ‖traceClassDualOp f x‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖traceClassDualOp f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [pow_two, ← mul_assoc] at hb
    exact (mul_le_mul_iff_of_pos_right hp).mp hb

/-- Positivity of both factors makes their analytic trace pairing positive. -/
theorem tracePairing_nonneg (T : TraceClass H) (hT : 0 ≤ T.1)
    (A : H →L[ℂ] H) (hA : 0 ≤ A) : 0 ≤ tracePairing T A := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hs := (positive_rankOne_series hT T.2 b).mapL (tracePairingCLM.flip A)
  change 0 ≤ (tracePairingCLM.flip A) (TraceClass.ofOperator T.1 T.2)
  rw [← hs.tsum_eq]
  apply tsum_nonneg
  intro i
  change 0 ≤ tracePairing (rankOneOperator _ _) A
  rw [tracePairing_rankOneOperator]
  exact (A.nonneg_iff_isPositive.mp hA).inner_nonneg_right _

/-- The actual Heisenberg adjoint of any bounded trace-class map. -/
def heisenbergDual (Φ : TraceClass H →L[ℂ] TraceClass K) :
    (K →L[ℂ] K) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun A := traceClassDualOp ((tracePairingCLM.flip A).comp Φ)
  map_add' A B := by
    ext x
    apply ext_inner_left ℂ
    intro y
    simp only [traceClassDualOp_inner, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, tracePairingCLM_apply,
      ContinuousLinearMap.add_apply, inner_add_right, map_add]
  map_smul' c A := by
    ext x
    apply ext_inner_left ℂ
    intro y
    simp only [traceClassDualOp_inner, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, tracePairingCLM_apply,
      ContinuousLinearMap.smul_apply, inner_smul_right, map_smul,
      RingHom.id_apply, smul_eq_mul]

/-- Exact Schrödinger–Heisenberg duality for every trace-class input. -/
theorem heisenbergDual_pairing (Φ : TraceClass H →L[ℂ] TraceClass K)
    (T : TraceClass H) (A : K →L[ℂ] K) :
    tracePairing T (heisenbergDual Φ A) = tracePairing (Φ T) A :=
  tracePairing_traceClassDualOp _ T

@[simp] theorem heisenbergDual_inner (Φ : TraceClass H →L[ℂ] TraceClass K)
    (A : K →L[ℂ] K) (x y : H) :
    ⟪y, heisenbergDual Φ A x⟫_ℂ = tracePairing (Φ (rankOneOperator x y)) A :=
  traceClassDualOp_inner _ x y

/-- The Heisenberg map preserves positive bounded operators whenever the
Schrödinger map preserves positive trace-class operators. -/
theorem heisenbergDual_nonneg (Φ : TraceClass H →L[ℂ] TraceClass K)
    (hΦ : ∀ T, 0 ≤ T.1 → 0 ≤ (Φ T).1)
    (A : K →L[ℂ] K) (hA : 0 ≤ A) : 0 ≤ heisenbergDual Φ A := by
  apply nonneg_of_inner_nonneg
  intro x
  rw [heisenbergDual_inner]
  apply tracePairing_nonneg _ (hΦ _ _) A hA
  exact (InnerProductSpace.rankOne ℂ x x).nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self x)

@[simp] theorem tracePairing_one (T : TraceClass H) :
    tracePairing T (1 : H →L[ℂ] H) = traceCLM T := by
  change trace (T.1 * 1) _ = trace T.1 T.2
  simp only [mul_one]

/-- Trace preservation gives actual unitality of the reconstructed dual. -/
theorem heisenbergDual_unital (Φ : TraceClass H →L[ℂ] TraceClass K)
    (hΦ : ∀ T, traceCLM (Φ T) = traceCLM T) :
    heisenbergDual Φ (1 : K →L[ℂ] K) = 1 := by
  apply tracePairing_separates
  intro T
  rw [heisenbergDual_pairing, tracePairing_one, tracePairing_one, hΦ]

/-- Normality in its defining ultraweak form: convergence against every
trace-class test is preserved, for arbitrary nets, with no boundedness premise. -/
theorem heisenbergDual_normal (Φ : TraceClass H →L[ℂ] TraceClass K)
    {ι : Type*} {l : Filter ι} {A : ι → K →L[ℂ] K} {B : K →L[ℂ] K}
    (hA : ∀ T : TraceClass K, Filter.Tendsto (fun i => tracePairing T (A i)) l
      (𝓝 (tracePairing T B))) (T : TraceClass H) :
    Filter.Tendsto (fun i => tracePairing T (heisenbergDual Φ (A i))) l
      (𝓝 (tracePairing T (heisenbergDual Φ B))) := by
  simpa only [heisenbergDual_pairing] using hA (Φ T)

/-- Cyclicity transports a bounded sandwich across the trace pairing. -/
theorem tracePairing_sandwich (T : TraceClass H) (P Q A : H →L[ℂ] H) :
    tracePairing (sandwichCLM P Q T) A = tracePairing T (Q * A * P) := by
  have hT : IsTraceClass (T.1 * (Q * A)) := by
    simpa using isTraceClass_mul_mul (A := (1 : H →L[ℂ] H)) (B := Q * A) T.2
  change trace (P * T.1 * Q * A) _ = trace (T.1 * (Q * A * P)) _
  simpa only [mul_assoc] using (trace_mul_cycle (A := P) hT)

/-- Covariance is inherited by the actual Heisenberg adjoint, with the usual
reversed conjugations. No dual covariance premise is assumed. -/
theorem heisenbergDual_covariance (Φ : TraceClass H →L[ℂ] TraceClass K)
    (U : H →L[ℂ] H) (V : K →L[ℂ] K)
    (hΦ : ∀ T, Φ (sandwichCLM U (star U) T) = sandwichCLM V (star V) (Φ T))
    (A : K →L[ℂ] K) :
    star U * heisenbergDual Φ A * U = heisenbergDual Φ (star V * A * V) := by
  apply tracePairing_separates
  intro T
  rw [← tracePairing_sandwich, heisenbergDual_pairing, hΦ,
    tracePairing_sandwich, heisenbergDual_pairing]

/-- The normal, positive and unital Heisenberg adjoint of an actual quantum
channel; continuity is derived from its original positivity and trace law. -/
def QuantumChannel.heisenberg (Φ : QuantumChannel H K) :
    (K →L[ℂ] K) →ₗ[ℂ] (H →L[ℂ] H) :=
  heisenbergDual Φ.toPositiveTracePreservingMap.toContinuousLinearMap

@[simp] theorem QuantumChannel.heisenberg_pairing (Φ : QuantumChannel H K)
    (T : TraceClass H) (A : K →L[ℂ] K) :
    tracePairing T (Φ.heisenberg A) = tracePairing (Φ.toLinearMap T) A :=
  heisenbergDual_pairing _ T A

@[simp] theorem QuantumChannel.heisenberg_unital (Φ : QuantumChannel H K) :
    Φ.heisenberg (1 : K →L[ℂ] K) = 1 :=
  heisenbergDual_unital _ Φ.trace_preserving

end Cloning.InfiniteTraceClass
