import Cloning.PCTWernerMixture

/-! A concrete finite-register partial trace as an actual CPTP map on the
trace-class Banach space. Its matrix entries are the ordinary spectator-index
sum, so it can be used directly in physical Gaussian-mixture limits. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass
namespace Cloning.PCT
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

abbrev Register (A : Type*) := lp (fun _ : A => ℂ) 2

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def registerBasis (A : Type*) : HilbertBasis A ℂ (Register A) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (Register A))

@[simp] theorem registerBasis_apply (a : A) :
    registerBasis A a = lp.single 2 a 1 :=
  ((registerBasis A).repr_symm_single a).symm

theorem register_inner_single (a : A) (x : Register A) :
    ⟪lp.single 2 a 1, x⟫_ℂ = x a := by
  simp [lp.inner_single_left, RCLike.inner_apply]

theorem environment_orthonormal (b : B) :
    Orthonormal ℂ (fun a : A => (lp.single 2 (a, b) 1 : Register (A × B))) := by
  rw [orthonormal_iff_ite]
  intro a c
  simp [register_inner_single, lp.single_apply, Pi.single_apply]

def environmentEmbedding (b : B) : Register A →ₗᵢ[ℂ] Register (A × B) :=
  (environment_orthonormal (A := A) b).orthogonalFamily.linearIsometry

theorem environmentEmbedding_single (b : B) (a : A) :
    environmentEmbedding b (lp.single 2 a 1) = lp.single 2 (a, b) 1 := by
  rw [environmentEmbedding, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

def environmentSlice (b : B) : Register (A × B) →L[ℂ] Register A :=
  (environmentEmbedding b).toContinuousLinearMap.adjoint

@[simp] theorem environmentSlice_apply (b : B) (x : Register (A × B)) (a : A) :
    environmentSlice b x a = x (a, b) := by
  rw [← register_inner_single]
  change ⟪lp.single 2 a 1, (environmentEmbedding b).toContinuousLinearMap.adjoint x⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪environmentEmbedding b (lp.single 2 a 1), x⟫_ℂ = _
  rw [environmentEmbedding_single, register_inner_single]

@[simp] theorem environmentSlice_adjoint_single (b : B) (a : A) :
    (environmentSlice b).adjoint (lp.single 2 a 1) = lp.single 2 (a, b) 1 := by
  rw [environmentSlice, ContinuousLinearMap.adjoint_adjoint]
  exact environmentEmbedding_single b a

/-- The literal finite Kraus sum with Kraus maps `I ⊗ ⟨b|`. -/
def partialTraceLinear : TraceClass (Register (A × B)) →ₗ[ℂ] TraceClass (Register A) :=
  ∑ b : B, conjugationLinearMap (environmentSlice b)

theorem partialTraceLinear_coefficient (X : TraceClass (Register (A × B))) (a c : A) :
    (partialTraceLinear X).1 (lp.single 2 c 1) a =
      ∑ b : B, X.1 (lp.single 2 (c, b) 1) (a, b) := by
  change inclusionCLM (partialTraceLinear X) (lp.single 2 c 1) a = _
  simp only [partialTraceLinear, LinearMap.sum_apply, map_sum,
    ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  change environmentSlice b (X.1 ((environmentSlice b).adjoint (lp.single 2 c 1))) a = _
  rw [environmentSlice_adjoint_single, environmentSlice_apply]

theorem traceCLM_register (X : TraceClass (Register A)) :
    traceCLM X = ∑ a : A, X.1 (lp.single 2 a 1) a := by
  letI : FiniteDimensional ℂ (Register A) :=
    (registerBasis A).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  change trace X.1 X.2 = _
  rw [trace_eq_linearMap_trace_of_finiteDimensional]
  simpa only [HilbertBasis.coe_toOrthonormalBasis, ContinuousLinearMap.coe_coe,
    registerBasis_apply, register_inner_single] using
    LinearMap.trace_eq_sum_inner X.1.toLinearMap (registerBasis A).toOrthonormalBasis

theorem partialTraceLinear_trace (X : TraceClass (Register (A × B))) :
    traceCLM (partialTraceLinear X) = traceCLM X := by
  rw [traceCLM_register, traceCLM_register]
  simp only [partialTraceLinear_coefficient, Fintype.sum_prod_type]

theorem partialTraceLinear_nonneg (X : TraceClass (Register (A × B))) (hX : 0 ≤ X.1) :
    0 ≤ (partialTraceLinear X).1 := by
  change 0 ≤ inclusionCLM (partialTraceLinear X)
  simp only [partialTraceLinear, LinearMap.sum_apply, map_sum]
  exact Finset.sum_nonneg (fun b _ => conjugationLinearMap_nonneg _ X hX)

theorem partialTraceLinear_completelyPositive :
    IsCompletelyPositive (partialTraceLinear (A := A) (B := B)) := by
  classical
  have hs (t : Finset B) : IsCompletelyPositive
      (∑ b ∈ t, conjugationLinearMap (environmentSlice (A := A) b)) := by
    induction t using Finset.induction_on with
    | empty =>
      intro n X hX x
      simp
    | @insert b t hb ih =>
      simpa only [Finset.sum_insert hb] using
        (conjugationLinearMap_completelyPositive (environmentSlice b)).add ih
  exact hs Finset.univ

/-- The actual partial trace, including complete positivity at every ancilla
size and exact trace preservation on all complex trace-class inputs. -/
def partialTraceChannel : QuantumChannel (Register (A × B)) (Register A) where
  toLinearMap := partialTraceLinear
  map_nonneg := partialTraceLinear_nonneg
  trace_preserving := partialTraceLinear_trace
  completelyPositive := partialTraceLinear_completelyPositive

theorem partialTraceChannel_vectorProjector (x : Register (A × B)) :
    partialTraceChannel.toLinearMap (vectorProjector x) =
      ∑ b : B, vectorProjector (environmentSlice b x) := by
  simp only [partialTraceChannel, partialTraceLinear, LinearMap.sum_apply,
    conjugationLinearMap_vectorProjector]

end Cloning.PCT
