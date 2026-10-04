import Cloning.WeylMultimodeContinuity
import Cloning.WeylChannel
import Cloning.InfiniteIsometricChannel
import Mathlib.Analysis.Normed.Group.Tannery

/-! Genuine trace-class Weyl conjugations: CPTP realization, exact coherent
translation, and continuity in the actual trace norm. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
open Filter

namespace Cloning.MultimodeCoherent
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ}

@[simp] theorem displacement_adjoint (a : Fin d → ℂ) :
    (displacement a).adjoint = displacement (-a) :=
  (weylUnitary a).adjoint_eq_symm

/-- The physical displacement as a genuine infinite-dimensional CPTP map. -/
def displacementChannel (a : Fin d → ℂ) : QuantumChannel (Fock d) (Fock d) :=
  QuantumChannel.ofIsometry (weylUnitary a).toLinearIsometry

/-- The same conjugation as a continuous map for the trace norm. -/
def displacementTraceMap (a : Fin d → ℂ) : TraceClass (Fock d) →L[ℂ] TraceClass (Fock d) :=
  sandwichCLM (displacement a) (displacement (-a))

theorem displacementTraceMap_eq_channel (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    displacementTraceMap a A = (displacementChannel a).toLinearMap A := by
  apply Subtype.ext
  ext v : 1
  change displacement a (A.1 (displacement (-a) v)) =
    displacement a (A.1 ((displacement a).adjoint v))
  rw [displacement_adjoint]

@[simp] theorem displacementTraceMap_vectorProjector (a : Fin d → ℂ) (v : (Fock d)) :
    displacementTraceMap a (vectorProjector v) = vectorProjector (displacement a v) := by
  rw [displacementTraceMap_eq_channel]
  exact QuantumChannel.ofIsometry_vectorProjector (weylUnitary a).toLinearIsometry v

lemma vectorProjector_phase (c : ℂ) (hc : ‖c‖ = 1) (v : (Fock d)) :
    vectorProjector (c • v) = vectorProjector v := by
  apply Subtype.ext
  ext y : 1
  change ⟪c • v, y⟫_ℂ • (c • v) = ⟪v, y⟫_ℂ • v
  rw [inner_smul_left, smul_smul]
  have h : starRingEnd ℂ c * c = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [mul_assoc, mul_comm ⟪v, y⟫_ℂ c, ← mul_assoc, h, one_mul]

/-- Coherent density matrices transform by literal phase-space translation. -/
theorem displacementTraceMap_coherentProjector (a z : Fin d → ℂ) :
    displacementTraceMap a (coherentProjector z) = coherentProjector (a + z) := by
  change displacementTraceMap a (vectorProjector (coherentVector z)) = _
  rw [displacementTraceMap_vectorProjector, displacement_coherentVector,
    vectorProjector_phase _ (displacementPhase_norm a z)]
  rfl

@[simp] theorem displacementTraceMap_neg_cancel (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    displacementTraceMap (-a) (displacementTraceMap a A) = A := by
  apply Subtype.ext
  ext v : 1
  change displacement (-a) (displacement a
    (A.1 (displacement (-a) (displacement (-(-a)) v)))) = A.1 v
  simp

lemma displacement_opNorm_le (a : Fin d → ℂ) : ‖displacement a‖ ≤ 1 :=
  (displacement a).opNorm_le_bound zero_le_one (fun v => by simp [displacement_norm])

lemma displacementTraceMap_norm_le (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    ‖displacementTraceMap a A‖ ≤ ‖A‖ := by
  change traceNorm ((displacement a) * A.1 * (displacement (-a))) _ ≤ traceNorm A.1 A.2
  calc
    _ ≤ ‖displacement a‖ * traceNorm A.1 A.2 * ‖displacement (-a)‖ :=
      traceNorm_mul_mul_le A.2 _
    _ ≤ 1 * traceNorm A.1 A.2 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (displacement_opNorm_le a)
        (traceNorm_nonneg _ _)) (displacement_opNorm_le (-a)) (norm_nonneg _)
        (mul_nonneg zero_le_one (traceNorm_nonneg _ _))
    _ = _ := by ring

/-- Unitary Weyl conjugation preserves trace norm for every trace-class
operator, including nonself-adjoint inputs. -/
theorem displacementTraceMap_norm (a : Fin d → ℂ) (A : TraceClass (Fock d)) :
    ‖displacementTraceMap a A‖ = ‖A‖ := by
  apply le_antisymm (displacementTraceMap_norm_le a A)
  simpa using displacementTraceMap_norm_le (-a) (displacementTraceMap a A)

lemma displacementPhase_neg_swap (a b : Fin d → ℂ) :
    displacementPhase (-b) (-a) = starRingEnd ℂ (displacementPhase a b) := by
  simp only [displacementPhase, Pi.neg_apply, ComplexCoherent.displacementPhase_neg_swap,
    map_prod]

/-- Scalar Weyl phases cancel in conjugation, giving an exact additive action
on the entire trace class. -/
theorem displacementTraceMap_add (a b : Fin d → ℂ) (A : TraceClass (Fock d)) :
    displacementTraceMap a (displacementTraceMap b A) = displacementTraceMap (a + b) A := by
  have hcomp (a b : Fin d → ℂ) (v : (Fock d)) : displacement a (displacement b v) =
      displacementPhase a b • displacement (a + b) v := by
    exact congrArg (fun T : (Fock d) →L[ℂ] (Fock d) => T v) (displacement_comp a b)
  apply Subtype.ext
  ext v : 1
  change displacement a (displacement b (A.1 (displacement (-b) (displacement (-a) v)))) =
    displacement (a + b) (A.1 (displacement (-(a + b)) v))
  rw [hcomp, hcomp, displacementPhase_neg_swap]
  simp only [map_smul, smul_smul]
  have hp : displacementPhase a b * starRingEnd ℂ (displacementPhase a b) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, displacementPhase_norm]
    norm_num
  rw [hp, one_smul]
  rw [show -b + -a = -(a + b) by abel]

/-- Strong Hilbert-space continuity upgrades to trace-norm continuity on every
positive trace-class input by the proved rank-one series and domination. -/
theorem continuous_displacementTraceMap_of_nonneg (A : TraceClass (Fock d)) (hA : 0 ≤ A.1) :
    Continuous (fun a => displacementTraceMap a A) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (Fock d)
  let v : w → (Fock d) := fun i => CFC.sqrt A.1 (b i)
  have hseries : HasSum (fun i => vectorProjector (v i)) A := positive_rankOne_series hA A.2 b
  have hmass : Summable (fun i => ‖vectorProjector (v i)‖) :=
    (positive_rankOne_mass hA A.2 b).summable
  have hsum (a : Fin d → ℂ) : (∑' i, vectorProjector (displacement a (v i))) =
      displacementTraceMap a A := by
    have h := hseries.mapL (displacementTraceMap a)
    simpa only [displacementTraceMap_vectorProjector] using h.tsum_eq
  apply continuous_iff_continuousAt.mpr
  intro a
  have hconv : Tendsto (fun a => ∑' i, vectorProjector (displacement a (v i))) (𝓝 a)
      (𝓝 (∑' i, vectorProjector (displacement a (v i)))) := by
    apply tendsto_tsum_of_dominated_convergence hmass
    · intro i
      exact vectorProjector_tendsto ((continuous_displacement (v i)).tendsto a)
    · exact Eventually.of_forall (fun a i => by simp [norm_vectorProjector, displacement_norm])
  simpa only [hsum] using hconv

/-- The physical Weyl action is trace-norm continuous on all trace-class
operators, without any finite-energy or positivity restriction. -/
theorem continuous_displacementTraceMap (A : TraceClass (Fock d)) :
    Continuous (fun a => displacementTraceMap a A) := by
  have hself (B : TraceClass (Fock d)) (hB : IsSelfAdjoint B.1) :
      Continuous (fun a => displacementTraceMap a B) := by
    have h := (continuous_displacementTraceMap_of_nonneg _ (TraceClass.positivePart_nonneg B hB)).sub
      (continuous_displacementTraceMap_of_nonneg _ (TraceClass.negativePart_nonneg B hB))
    simpa only [← map_sub, TraceClass.positivePart_sub_negativePart B hB] using h
  have h := (hself _ (TraceClass.realComponent_isSelfAdjoint A)).add
    ((continuous_const : Continuous (fun _ : (Fin d → ℂ) => Complex.I)).smul
      (hself _ (TraceClass.imaginaryComponent_isSelfAdjoint A)))
  change Continuous (fun a => displacementTraceMap a (TraceClass.realComponent A) +
    Complex.I • displacementTraceMap a (TraceClass.imaginaryComponent A)) at h
  simpa only [← map_smul, ← map_add,
    TraceClass.realComponent_add_I_smul_imaginaryComponent A] using h

end Cloning.MultimodeCoherent
