import Cloning.HeisenbergDual
import Cloning.InfiniteIsometricChannel
import Cloning.WeylQuantumPositive
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The duality between positive bounded-operator blocks and positive
trace-class blocks. Finite ancillas are realized as actual Hilbert direct
sums, so positivity here includes all entangled finite-ancilla tests. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators

namespace Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Rectangular trace duality for a conjugation between different Hilbert spaces. -/
theorem tracePairing_conjugation (V : H →L[ℂ] K) (T : TraceClass H)
    (A : K →L[ℂ] K) :
    tracePairing (conjugationLinearMap V T) A =
      tracePairing T (V.adjoint.comp (A.comp V)) := by
  let f : TraceClass H →ₗ[ℂ] ℂ :=
    (tracePairingCLM.flip A).toLinearMap.comp (conjugationLinearMap V)
  let g : TraceClass H →ₗ[ℂ] ℂ :=
    (tracePairingCLM.flip (V.adjoint.comp (A.comp V))).toLinearMap
  have hpos (S : TraceClass H) (hS : 0 ≤ S.1) : f S = g S := by
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    have hf := (conjugationLinearMap_positive_hasSum V S hS b).mapL (tracePairingCLM.flip A)
    have hg := (positive_rankOne_series hS S.2 b).mapL
      (tracePairingCLM.flip (V.adjoint.comp (A.comp V)))
    have heq : (fun i : w => tracePairing (vectorProjector (V (CFC.sqrt S.1 (b i)))) A) =
        (fun i : w => tracePairing (vectorProjector (CFC.sqrt S.1 (b i)))
          (V.adjoint.comp (A.comp V))) := by
      funext i
      change tracePairing (rankOneOperator _ _) _ = tracePairing (rankOneOperator _ _) _
      simp only [tracePairing_rankOneOperator, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
    exact (show HasSum _ (f S) from hf).unique (heq ▸ (show HasSum _ (g S) from hg))
  have hsa (S : TraceClass H) (hS : IsSelfAdjoint S.1) : f S = g S := by
    rw [← TraceClass.positivePart_sub_negativePart S hS, map_sub, map_sub,
      hpos _ (TraceClass.positivePart_nonneg S hS),
      hpos _ (TraceClass.negativePart_nonneg S hS)]
  change f T = g T
  rw [← TraceClass.realComponent_add_I_smul_imaginaryComponent T,
    map_add, map_add, map_smul, map_smul,
    hsa _ (TraceClass.realComponent_isSelfAdjoint T),
    hsa _ (TraceClass.imaginaryComponent_isSelfAdjoint T)]

/-- A rectangular sandwich with distinct left and right factors, constructed
inside the genuine trace-class space by complex polarization. -/
def rectangularSandwich (V W : H →L[ℂ] K) (T : TraceClass H) : TraceClass K :=
  (1 / 4 : ℂ) • (conjugationLinearMap (V + W) T - conjugationLinearMap (V - W) T +
    Complex.I • (conjugationLinearMap (V + Complex.I • W) T -
      conjugationLinearMap (V - Complex.I • W) T))

theorem rectangularSandwich_coe (V W : H →L[ℂ] K) (T : TraceClass H) :
    (rectangularSandwich V W T).1 = V.comp (T.1.comp W.adjoint) := by
  change inclusionCLM (rectangularSandwich V W T) = _
  simp only [rectangularSandwich, map_smul, map_add, map_sub,
    inclusionCLM_apply, conjugationLinearMap_coe]
  ext x
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    operatorConjugation_apply, ContinuousLinearMap.comp_apply]
  have hI : (Complex.I • W).adjoint = -Complex.I • W.adjoint := by
    simpa using (map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℂ)) Complex.I W)
  simp only [map_add, map_sub, hI, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_smul]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

/-- Full rectangular cyclicity for the analytic trace pairing. -/
theorem tracePairing_rectangularSandwich (V W : H →L[ℂ] K) (T : TraceClass H)
    (A : K →L[ℂ] K) :
    tracePairing (rectangularSandwich V W T) A =
      tracePairing T (W.adjoint.comp (A.comp V)) := by
  change (tracePairingCLM.flip A) (rectangularSandwich V W T) = _
  simp only [rectangularSandwich, map_smul, map_add, map_sub,
    ContinuousLinearMap.flip_apply, tracePairingCLM_apply, tracePairing_conjugation]
  rw [← (tracePairing T).map_sub, ← (tracePairing T).map_sub,
    ← (tracePairing T).map_smul, ← (tracePairing T).map_add, ← (tracePairing T).map_smul]
  congr 1
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  have hI : (Complex.I • W).adjoint = -Complex.I • W.adjoint := by
    simpa using (map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℂ)) Complex.I W)
  simp only [map_add, map_sub, hI, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_smul]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual finite Hilbert direct sum used for an ancilla. -/
abbrev BlockHilbert (ι : Type*) (H : Type*) [Fintype ι]
    [NormedAddCommGroup H] := PiLp 2 (fun _ : ι => H)

/-- Coordinate injection into the finite Hilbert direct sum. -/
def blockInjection (i : ι) : H →L[ℂ] BlockHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

@[simp] theorem blockInjection_apply (i j : ι) (x : H) :
    blockInjection i x j = if j = i then x else 0 := by
  simp [blockInjection, Pi.single_apply]

@[simp] theorem blockInjection_adjoint_apply (i : ι) (x : BlockHilbert ι H) :
    (blockInjection i).adjoint x = x i := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, blockInjection_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Bounded matrix action on the entire finite Hilbert direct sum. -/
def blockOperator (A : ι → ι → H →L[ℂ] H) : BlockHilbert ι H →L[ℂ] BlockHilbert ι H :=
  ∑ i, ∑ j, (blockInjection i).comp ((A i j).comp (blockInjection j).adjoint)

theorem blockOperator_apply (A : ι → ι → H →L[ℂ] H) (x : BlockHilbert ι H) (i : ι) :
    blockOperator A x i = ∑ j, A i j (x j) := by
  simp [blockOperator, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum,
    ContinuousLinearMap.comp_apply, blockInjection_apply]

theorem blockOperator_quadratic (A : ι → ι → H →L[ℂ] H) (x : BlockHilbert ι H) :
    ⟪x, blockOperator A x⟫_ℂ = ∑ i, ∑ j, ⟪x i, A i j (x j)⟫_ℂ := by
  simp only [PiLp.inner_apply, blockOperator_apply, inner_sum]

theorem blockOperator_nonneg (A : ι → ι → H →L[ℂ] H)
    (hA : Cloning.BoundedOperator.BlockPositive A) : 0 ≤ blockOperator A := by
  apply nonneg_of_inner_nonneg
  intro x
  rw [blockOperator_quadratic]
  exact hA (fun i => x i)

@[simp] theorem blockOperator_compression (A : ι → ι → H →L[ℂ] H) (i j : ι) :
    (blockInjection i).adjoint.comp ((blockOperator A).comp (blockInjection j)) = A i j := by
  ext x
  simp [ContinuousLinearMap.comp_apply, blockOperator_apply, blockInjection_apply, apply_ite]

/-- A finite trace-class block is trace class on the actual Hilbert direct sum. -/
def traceClassBlock (B : ι → ι → TraceClass H) : TraceClass (BlockHilbert ι H) :=
  ∑ i, ∑ j, rectangularSandwich (blockInjection i) (blockInjection j) (B i j)

theorem traceClassBlock_coe (B : ι → ι → TraceClass H) :
    (traceClassBlock B).1 = blockOperator (fun i j => (B i j).1) := by
  change (inclusionCLM (H := BlockHilbert ι H)) (traceClassBlock B) = _
  simp only [traceClassBlock, map_sum, inclusionCLM_apply, rectangularSandwich_coe,
    blockOperator]

theorem traceClassBlock_nonneg (B : ι → ι → TraceClass H) (hB : BlockPositive B) :
    0 ≤ (traceClassBlock B).1 := by
  rw [traceClassBlock_coe]
  exact blockOperator_nonneg _ hB

/-- The exact block trace pairing, with the mandatory transposition of indices. -/
theorem tracePairing_block (B : ι → ι → TraceClass H) (A : ι → ι → H →L[ℂ] H) :
    tracePairing (traceClassBlock B) (blockOperator A) =
      ∑ i, ∑ j, tracePairing (B j i) (A i j) := by
  change ((tracePairingCLM (H := BlockHilbert ι H)).flip (blockOperator A))
    (traceClassBlock B) = _
  simp only [traceClassBlock, map_sum, ContinuousLinearMap.flip_apply,
    tracePairingCLM_apply, tracePairing_rectangularSandwich, blockOperator_compression]
  exact Finset.sum_comm

/-- Positive bounded and trace-class finite blocks have nonnegative dual
pairing. Neither block is assumed diagonal or a simple tensor. -/
theorem block_tracePairing_nonneg (B : ι → ι → TraceClass H)
    (hB : BlockPositive B) (A : ι → ι → H →L[ℂ] H)
    (hA : Cloning.BoundedOperator.BlockPositive A) :
    0 ≤ ∑ i, ∑ j, tracePairing (B j i) (A i j) := by
  rw [← tracePairing_block]
  exact tracePairing_nonneg _ (traceClassBlock_nonneg B hB) _ (blockOperator_nonneg A hA)

end Cloning.InfiniteTraceClass
