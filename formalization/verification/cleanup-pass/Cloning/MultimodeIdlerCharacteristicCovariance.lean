import Cloning.MultimodeIdlerCharacteristicIsometry
import Cloning.WeylSqueezerPartialTrace
import Cloning.PCTGaussianOutput
import Cloning.WeylQuantumPositiveBlocks

/-! The concrete occupation channel inherits conjugated Weyl covariance
from its proved two-output isometry. Both trace-class inputs and coherences
are retained throughout. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeIdler
open Cloning.InfiniteTraceClass Cloning.MultimodeCoherent
open Cloning.WeylSqueezerProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

lemma idlerSlice_appendedIsometry (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (m : Occupation d) (x : Fock d) :
    idlerSlice m (appendedIsometry q hq0 hq1 x) = kraus q hq0 hq1 m x := by
  ext k
  rw [show appendedIsometry q hq0 hq1 x = jointReindex d d (isometry q hq0 hq1 x) from rfl,
    idlerSlice_apply, jointReindex_apply]
  simp only [occupationSplit, Equiv.coe_fn_mk, Fin.append_left, Fin.append_right,
    kraus, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, slice_apply]

/-- Characteristic evaluation of the actual Kraus channel equals evaluation
of its actual Stinespring output on the second-register Weyl operator. -/
theorem channel_characteristic_joint (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (T : TraceClass (Fock d)) (b : Fin d → ℂ) :
    tracePairing ((channel q hq0 hq1).toLinearMap T) (displacement b) =
      tracePairing (conjugationLinearMap (appendedIsometry q hq0 hq1).toContinuousLinearMap T)
        (displacement (Fin.append 0 b)) := by
  rw [tracePairing_conjugation]
  suffices hpure : ∀ x : Fock d,
      tracePairing ((channel q hq0 hq1).toLinearMap (vectorProjector x)) (displacement b) =
        1 * ⟪x, (appendedIsometry q hq0 hq1).toContinuousLinearMap.adjoint
          (displacement (Fin.append 0 b) (appendedIsometry q hq0 hq1 x))⟫_ℂ by
    simpa only [one_mul] using Cloning.WeylSqueezer.channel_pairing_of_pure
      (channel q hq0 hq1) (displacement b)
      ((appendedIsometry q hq0 hq1).toContinuousLinearMap.adjoint.comp
        ((displacement (Fin.append 0 b)).comp
          (appendedIsometry q hq0 hq1).toContinuousLinearMap)) 1 hpure T
  intro x
  have hs := (channel_hasSum q hq0 hq1 (vectorProjector x)).mapL
    (tracePairingCLM.flip (displacement b))
  have ht := idlerSlice_inner_hasSum (appendedIsometry q hq0 hq1 x)
    (displacement (Fin.append 0 b) (appendedIsometry q hq0 hq1 x))
  simp only [idlerSlice_displacement, idlerSlice_appendedIsometry] at ht
  have he (m : Occupation d) :
      tracePairing (krausTerm (kraus q hq0 hq1 m) (vectorProjector x)) (displacement b) =
        ⟪kraus q hq0 hq1 m x, displacement b (kraus q hq0 hq1 m x)⟫_ℂ := by
    rw [krausTerm_vectorProjector]
    exact tracePairing_rankOneOperator _ _ _
  simp only [ContinuousLinearMap.flip_apply, tracePairingCLM_apply, he] at hs
  simpa only [one_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]
    using hs.unique ht

private theorem conjugation_comp
    {H K L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (V : K →L[ℂ] L) (W : H →L[ℂ] K) (T : TraceClass H) :
    conjugationLinearMap (V.comp W) T = conjugationLinearMap V (conjugationLinearMap W T) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  simp only [conjugationLinearMap_coe, operatorConjugation_apply,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

private theorem displacementTraceMap_eq_conjugation {e : ℕ} (a : Fin e → ℂ)
    (T : TraceClass (Cloning.MultimodeCoherent.Fock e)) :
    displacementTraceMap a T = conjugationLinearMap (displacement a) T := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change displacement a (T.1 (displacement (-a) x)) =
    displacement a (T.1 ((displacement a).adjoint x))
  rw [displacement_adjoint]

lemma appendedIsometry_conjugation (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (a : Fin d → ℂ) (T : TraceClass (Fock d)) :
    conjugationLinearMap (appendedIsometry q hq0 hq1).toContinuousLinearMap
      (displacementTraceMap a T) =
      displacementTraceMap (Fin.append (amplifierScale q a) (complementaryScale q (star a)))
        (conjugationLinearMap (appendedIsometry q hq0 hq1).toContinuousLinearMap T) := by
  rw [displacementTraceMap_eq_conjugation, displacementTraceMap_eq_conjugation,
    ← conjugation_comp, appendedIsometry_intertwines, conjugation_comp]

lemma weylCharacter_append_zero (x y b : Fin d → ℂ) :
    weylCharacter (Fin.append x y) (-(Fin.append 0 b)) = weylCharacter y (-b) := by
  have hn : -(Fin.append (0 : Fin d → ℂ) b) = Fin.append 0 (-b) := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Pi.neg_apply, Fin.append_left, Fin.append_right, Pi.zero_apply, neg_zero]
  rw [hn]
  simp only [weylCharacter, displacementPhase_append, displacementPhase_zero_right,
    displacementPhase_zero_left, one_mul]

/-- Exact conjugated displacement covariance of the negative-binomial channel. -/
theorem channel_weyl_covariant (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (a : Fin d → ℂ) (T : TraceClass (Fock d)) :
    (channel q hq0 hq1).toLinearMap (displacementTraceMap a T) =
      displacementTraceMap (complementaryScale q (star a)) ((channel q hq0 hq1).toLinearMap T) := by
  apply characteristic_injective
  funext b
  dsimp only
  rw [channel_characteristic_joint, appendedIsometry_conjugation,
    Cloning.PCTGaussianOutput.displacement_characteristic,
    Cloning.PCTGaussianOutput.displacement_characteristic,
    channel_characteristic_joint, weylCharacter_append_zero]

/-- The actual number Kraus columns on vacuum. -/
lemma kraus_vacuum (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (m : Occupation d) :
    kraus q hq0 hq1 m (numberBasis d 0) =
      (Real.sqrt (Cloning.ThermalWitness.productGeometric q m):ℂ) • numberBasis d m := by
  ext k
  rw [kraus_numberBasis_apply]
  simp only [zero_add, numberBasis_eq_single, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : m=k
  · subst k
    simp [Cloning.MultimodeAmplifier.productLaw_zero]
  · simp [h, Ne.symm h]

/-- Its vacuum output is literally the normalized product thermal state. -/
theorem channel_vacuum (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (channel q hq0 hq1).toLinearMap (coherentProjector (0 : Fin d → ℂ)) =
      vectorMixture (Cloning.MultimodeCoherentGaussianMixture.numberBasis d)
        (Cloning.ThermalWitness.productGeometric q) := by
  have h := channel_hasSum q hq0 hq1 (vectorProjector (numberBasis d 0))
  simp only [krausTerm_vectorProjector, kraus_vacuum] at h
  have he (k : Occupation d) : vectorProjector
      ((Real.sqrt (Cloning.ThermalWitness.productGeometric q k):ℂ) • numberBasis d k) =
      (Cloning.ThermalWitness.productGeometric q k : ℂ) • vectorProjector (numberBasis d k) :=
    Cloning.BosonicAmplifier.vectorProjector_sqrt_smul _
      (Cloning.ThermalWitness.productGeometric_nonneg hq0 hq1 k) _
  simp only [he] at h
  change (channel q hq0 hq1).toLinearMap (vectorProjector (coherentVector 0)) = _
  rw [Cloning.MultimodeAmplifier.coherentVector_zero_eq_numberBasis]
  exact h.tsum_eq.symm

end Cloning.MultimodeIdler
