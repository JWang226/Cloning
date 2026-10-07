import Cloning.WernerPhysicalOperator
import Cloning.IsometricRecovery
import Cloning.InfiniteOccupationStates

/-! # Physical Werner occupation pullback and its trace-norm limit

The occupation coordinate isometry is extended to a CPTP compression on the
whole computational tensor space. Applied to the original Werner sandwich
operator, it gives exactly the already-formalized finite-support Fock
occupation state. This closes the physical-output identification required
for the general-dimensional Werner thermal limit.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter

namespace Cloning.GeneralSymmetricOccupation
open Cloning.InfiniteTraceClass

/-- Excitation occupations, with basis letter zero chosen as the reference. -/
def excitation {L s : ℕ} (q : Occupation L (s + 1)) : Fin s → ℕ :=
  fun i => q.val i.succ

theorem occupation_sum {L d : ℕ} (q : Occupation L d) : ∑ a, q.val a = L := by
  obtain ⟨w, hw⟩ := q.property
  rw [← hw]
  exact profile_sum w

theorem reference_add_excitation {L s : ℕ} (q : Occupation L (s + 1)) :
    q.val 0 + ∑ i, excitation q i = L := by
  simpa [Fin.sum_univ_succ, excitation] using occupation_sum q

theorem excitation_sum_le {L s : ℕ} (q : Occupation L (s + 1)) :
    (∑ i, excitation q i) ≤ L := by
  have h := reference_add_excitation q
  omega

theorem reference_eq_sub_excitation {L s : ℕ} (q : Occupation L (s + 1)) :
    q.val 0 = L - ∑ i, excitation q i := by
  have h := reference_add_excitation q
  omega

theorem excitation_injective (L s : ℕ) : Function.Injective (@excitation L s) := by
  intro q r h
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [reference_eq_sub_excitation, reference_eq_sub_excitation, h]
  · exact congrFun h j

/-- Restoring the reference occupation to an admissible excitation index. -/
def fromExcitation {L s : ℕ} (k : Fin s → ℕ) (hk : (∑ i, k i) ≤ L) :
    Occupation L (s + 1) :=
  (compositionEquiv L (s + 1)).symm
    ⟨Fin.cons (L - ∑ i, k i) k, by simp [Fin.sum_univ_succ, Nat.sub_add_cancel hk]⟩

@[simp] theorem excitation_fromExcitation {L s : ℕ} (k : Fin s → ℕ)
    (hk : (∑ i, k i) ≤ L) : excitation (fromExcitation k hk) = k := by
  funext i
  simp [excitation, fromExcitation, compositionEquiv]

abbrev FockSpace (s : ℕ) := lp (fun _ : Fin s → ℕ => ℂ) 2

def numberVector {s : ℕ} (k : Fin s → ℕ) : FockSpace s := lp.single 2 k 1

theorem numberVector_norm {s : ℕ} (k : Fin s → ℕ) : ‖numberVector k‖ = 1 := by
  rw [numberVector, lp.norm_single (by norm_num)]
  simp

theorem finite_number_orthonormal (L s : ℕ) :
    Orthonormal ℂ (fun q : Occupation L (s + 1) => numberVector (excitation q)) := by
  rw [orthonormal_iff_ite]
  intro q r
  rw [numberVector, lp.inner_single_left]
  simp only [numberVector, RCLike.inner_apply, lp.single_apply, Pi.single_apply]
  by_cases h : q = r
  · simp [h]
  · have hx : excitation q ≠ excitation r := fun he => h (excitation_injective L s he)
    simp [h, hx]

/-- Zero-padding the finite occupation register into full multimode Fock space. -/
def occupationPad (L s : ℕ) : OccupationSpace L (s + 1) →ₗᵢ[ℂ] FockSpace s :=
  (finite_number_orthonormal L s).orthogonalFamily.linearIsometry

theorem occupationPad_single (L s : ℕ) (q : Occupation L (s + 1)) :
    occupationPad L s (lp.single 2 q 1) = numberVector (excitation q) := by
  rw [occupationPad, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

/-- The finite occupation density selected as replacement for nonsymmetric mass. -/
def vacuumRegister (L s : ℕ) : DensityState (OccupationSpace L (s + 1)) :=
  DensityState.pure (lp.single 2 (label (fun _ : Fin L => (0 : Fin (s + 1)))) 1)
    (by rw [lp.norm_single (by norm_num)]; simp)

/-- A genuine CPTP occupation pullback defined for every tensor-space input. -/
def occupationRecovery (L s : ℕ) : QuantumChannel (TensorSpace L (s + 1)) (FockSpace s) :=
  (QuantumChannel.ofIsometry (occupationPad L s)).comp
    (QuantumChannel.isometricRecovery (isometry L (s + 1)) (vacuumRegister L s))

theorem occupationRecovery_column (L s : ℕ) (q : Occupation L (s + 1)) :
    (occupationRecovery L s).toLinearMap (vectorProjector (column q)) =
      vectorProjector (numberVector (excitation q)) := by
  rw [← isometry_single]
  change (QuantumChannel.ofIsometry (occupationPad L s)).toLinearMap
    ((QuantumChannel.isometricRecovery (isometry L (s + 1)) (vacuumRegister L s)).toLinearMap
      (vectorProjector (isometry L (s + 1) (lp.single 2 q 1)))) = _
  rw [QuantumChannel.isometricRecovery_vectorProjector,
    QuantumChannel.ofIsometry_vectorProjector, occupationPad_single]

/-- Werner's pure-product output as an actual trace-class operator. -/
def wernerOutput {L s : ℕ} (S : Finset (Fin L)) : TraceClass (TensorSpace L (s + 1)) :=
  ∑ q : Occupation L (s + 1),
    ((((q.val 0).choose S.card : ℝ) / (L + s).choose (S.card + s) : ℝ) : ℂ) •
      vectorProjector (column q)

/-- The bundled trace-class output is exactly the physical symmetric sandwich. -/
theorem wernerOutput_op {L s : ℕ} (S : Finset (Fin L)) :
    (wernerOutput (s := s) S).1 = wernerOutputOperator (0 : Fin (s + 1)) S := by
  rw [wernerOutputOperator_eq_sum]
  change inclusionCLM (wernerOutput S) = _
  simp only [wernerOutput, map_sum, map_smul]
  rfl

/-- The physical eigenvalue agrees with the full padded Fock occupation law. -/
theorem wernerWeight_eq_occupationLaw {L s : ℕ} (S : Finset (Fin L))
    (q : Occupation L (s + 1)) :
    ((q.val 0).choose S.card : ℝ) / (L + s).choose (S.card + s) =
      Cloning.WernerNormalization.occupationLaw S.card L s (excitation q) := by
  rw [Cloning.WernerNormalization.occupationLaw, reference_eq_sub_excitation]
  split_ifs with hk
  · exact Cloning.WernerAsymptotics.coefficient_eq_wernerWeight S.card L s _
  · have hn : L - ∑ i, excitation q i < S.card := by
      have hs := excitation_sum_le q
      have hSL : S.card ≤ L := by simpa using Finset.card_le_univ S
      omega
    simp [Nat.choose_eq_zero_of_lt hn]

/-- Exact channel-level identification with the finite Werner Fock operator. -/
theorem occupationRecovery_wernerOutput {L s : ℕ} (S : Finset (Fin L)) :
    (occupationRecovery L s).toLinearMap (wernerOutput (s := s) S) =
      Cloning.InfiniteOccupationStates.occupationOperator (@numberVector s) S.card L := by
  classical
  simp only [wernerOutput, map_sum, map_smul, occupationRecovery_column]
  have hw : ∀ q : Occupation L (s + 1),
      ((((q.val 0).choose S.card : ℝ) / (L + s).choose (S.card + s) : ℝ) : ℂ) =
        (Cloning.WernerNormalization.occupationLaw S.card L s (excitation q) : ℂ) := by
    intro q
    exact_mod_cast wernerWeight_eq_occupationLaw S q
  simp_rw [hw]
  unfold Cloning.InfiniteOccupationStates.occupationOperator vectorMixture
  rw [tsum_eq_sum (s := Cloning.WernerNormalization.occupationSupport s L)]
  · apply Finset.sum_bij (fun q _ => excitation q)
    · intro q hq
      exact Cloning.WernerNormalization.mem_occupationSupport.mpr (excitation_sum_le q)
    · intro q hq r hr hqr
      exact excitation_injective L s hqr
    · intro k hk
      let q := fromExcitation k (Cloning.WernerNormalization.mem_occupationSupport.mp hk)
      exact ⟨q, Finset.mem_univ q, excitation_fromExcitation k _⟩
    · intro q hq
      rfl
  · intro k hk
    have hk' : ¬ (∑ i, k i) ≤ L - S.card := by
      intro h
      apply hk
      exact Cloning.WernerNormalization.mem_occupationSupport.mpr (h.trans (Nat.sub_le _ _))
    simp [Cloning.WernerNormalization.occupationLaw, hk']

end Cloning.GeneralSymmetricOccupation

namespace Cloning.GeneralSymmetricOccupation
open Cloning.InfiniteTraceClass

/-- The first `n` slots of an `m`-fold physical tensor product. -/
def inputSlots (n m : ℕ) (hnm : n ≤ m) : Finset (Fin m) :=
  Finset.univ.map ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩

@[simp] theorem inputSlots_card (n m : ℕ) (hnm : n ≤ m) :
    (inputSlots n m hnm).card = n := by simp [inputSlots]

theorem mem_inputSlots (n m : ℕ) (hnm : n ≤ m) (i : Fin m) :
    i ∈ inputSlots n m hnm ↔ i.val < n := by
  classical
  simp only [inputSlots, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

/-- Positivity of the physical Werner output has no additional hypothesis. -/
theorem wernerOutput_nonneg {L s : ℕ} (S : Finset (Fin L)) :
    0 ≤ (wernerOutput (s := s) S).1 := by
  have heq : wernerOutput (s := s) S = vectorMixture (@column L (s + 1))
      (fun q => ((q.val 0).choose S.card : ℝ) / (L + s).choose (S.card + s)) := by
    simp only [vectorMixture, tsum_fintype, wernerOutput]
  rw [heq]
  exact vectorMixture_nonneg _ column_norm _ (hasSum_fintype _).summable
    (fun _ => by positivity)

/-- Unit trace follows from the exact CPTP pullback and the proved Werner law. -/
theorem wernerOutput_trace_one {L s : ℕ} (hs : 1 ≤ s) (S : Finset (Fin L)) :
    traceCLM (wernerOutput (s := s) S) = 1 := by
  have htp :=
    (traceCLM_apply ((occupationRecovery L s).toLinearMap (wernerOutput (s := s) S))).trans
      (((occupationRecovery L s).trace_preserving (wernerOutput (s := s) S)).trans
        (traceCLM_apply (wernerOutput (s := s) S)).symm)
  rw [← htp, occupationRecovery_wernerOutput]
  change traceCLM (vectorMixture (@numberVector s)
    (Cloning.WernerNormalization.occupationLaw S.card L s)) = 1
  rw [traceCLM_vectorMixture _ numberVector_norm _
    (Cloning.InfiniteOccupationStates.occupationLaw_summable _ _ _),
    (Cloning.WernerNormalization.occupationLaw_hasSum S.card L s
      (by simpa using Finset.card_le_univ S) hs).tsum_eq]
  simp

/-- A concrete normalized density state equal to Werner's original formula. -/
def wernerOutputState {L s : ℕ} (hs : 1 ≤ s) (S : Finset (Fin L)) :
    DensityState (TensorSpace L (s + 1)) where
  op := (wernerOutput (s := s) S).1
  positive := wernerOutput_nonneg S
  traceClass := (wernerOutput (s := s) S).2
  trace_one := wernerOutput_trace_one hs S

/-- The general-dimensional physical Werner output, pulled back by an actual
channel, converges in trace norm to the multimode thermal density operator.
No physical-occupation identification or coefficient-convergence assumption
remains: only the cloning-ratio hypothesis is required. -/
theorem physical_werner_thermal_limit {s : ℕ} (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ (occupationRecovery (m n) s).toLinearMap
      (wernerOutput (s := s) (inputSlots n (m n) (hm n)))) atTop
      (𝓝 (Cloning.InfiniteOccupationStates.thermalOperator (@numberVector s) γ)) := by
  simp only [occupationRecovery_wernerOutput, inputSlots_card]
  exact Cloning.InfiniteOccupationStates.occupationOperator_tendsto hs _ numberVector_norm m hγ h

/-- The same physical channel limit written explicitly as trace-norm error. -/
theorem physical_werner_traceNorm_limit {s : ℕ} (hs : 1 ≤ s)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n ↦ ‖(occupationRecovery (m n) s).toLinearMap
      (wernerOutput (s := s) (inputSlots n (m n) (hm n))) -
        Cloning.InfiniteOccupationStates.thermalOperator (@numberVector s) γ‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (physical_werner_thermal_limit hs m hm hγ h)

end Cloning.GeneralSymmetricOccupation
