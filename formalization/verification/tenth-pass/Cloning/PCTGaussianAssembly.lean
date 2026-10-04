import Cloning.PCTPhysicalWerner

/-! Frame-independent physical purification-cloning-tracing and its Gaussian
reduced-product mixture. Environmental probability/Haar randomization cancels
exactly, and the trace-norm limit starts from Werner's literal sandwich. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass
namespace Cloning.PCT
open GeneralSymmetricOccupation GeneralCoherent
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem fullFrame_of_orthonormal {s : ℕ} (hcard : Fintype.card C = s + 1)
    {u : Fin (s + 1) → Register C} (hu : Orthonormal ℂ u) :
    ∃ b : OrthonormalBasis (Fin (s + 1)) ℂ (Register C), (b : Fin (s + 1) → Register C) = u := by
  letI : FiniteDimensional ℂ (Register C) :=
    (registerBasis C).toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hc : Module.finrank ℂ (Register C) = Fintype.card (Fin (s + 1)) := by
    rw [Module.finrank_eq_card_basis (registerBasis C).toOrthonormalBasis.toBasis]
    simpa using hcard
  have hv : Orthonormal ℂ ((Set.univ : Set (Fin (s + 1))).restrict u) :=
    hu.comp _ Subtype.val_injective
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hc
  exact ⟨b, funext fun i => hb i (Set.mem_univ i)⟩

/-- Werner's original physical output on a pure tensor input, defined using
only the input vector and the canonical physical symmetric projector. -/
def pureWernerOperator {L : ℕ} (s : ℕ) (ψ : Register C) (S : Finset (Fin L)) :
    Register (Fin L → C) →L[ℂ] Register (Fin L → C) :=
  (((Nat.choose (S.card + s) s : ℝ) / Nat.choose (L + s) s : ℝ) : ℂ) •
    (physicalProjector L * pureSlotsOperator ψ S * physicalProjector L)

theorem pureWernerOperator_traceClass {L s : ℕ} (hcard : Fintype.card C = s + 1)
    (ψ : Register C) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    IsTraceClass (pureWernerOperator s ψ S) := by
  obtain ⟨b, hb⟩ := exists_purification_frame hcard ψ hψ
  have he := wernerOutput_physical_purification b S
  rw [hb] at he
  change IsTraceClass (_ • _)
  rw [← he]
  exact ((QuantumChannel.ofIsometry (tensorFrame b.orthonormal L)).toLinearMap
    (wernerOutput (s := s) S)).2

def pureWernerOutput {L s : ℕ} (hcard : Fintype.card C = s + 1)
    (ψ : Register C) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) : TraceClass (Register (Fin L → C)) :=
  TraceClass.ofOperator (pureWernerOperator s ψ S) (pureWernerOperator_traceClass hcard ψ hψ S)

theorem pureWernerOutput_eq_frame {L s : ℕ} (hcard : Fintype.card C = s + 1)
    {u : Fin (s + 1) → Register C} (hu : Orthonormal ℂ u) (S : Finset (Fin L)) :
    pureWernerOutput hcard (u 0) (hu.norm_eq_one 0) S =
      (QuantumChannel.ofIsometry (tensorFrame hu L)).toLinearMap (wernerOutput (s := s) S) := by
  obtain ⟨b, hb⟩ := fullFrame_of_orthonormal hcard hu
  cases hb
  apply Subtype.ext
  exact (wernerOutput_physical_purification b S).symm

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The actual one-particle reduced density matrix of a purification. -/
def reducedDensityMatrix (ψ : Register (A × B)) : Matrix A A ℂ :=
  fun a c => ∑ b, ψ (a, b) * star (ψ (c, b))

/-- A literal tensor power of a finite matrix, lifted to the physical
trace-class space in its computational word basis. -/
def matrixTensorPower (ρ : Matrix A A ℂ) (L : ℕ) : TraceClass (Register (Fin L → A)) :=
  InfiniteFiniteCorner.matrixLift (registerBasis (Fin L → A))
    (fun a c => ∏ i, ρ (a i) (c i))

theorem partialTrace_product_eq_matrixTensorPower (ψ : Register (A × B)) (L : ℕ) :
    partialTraceChannel.toLinearMap (vectorProjector
      (regroup L (tensorVector (fun _ : Fin L => ψ)))) =
      matrixTensorPower (reducedDensityMatrix ψ) L := by
  apply Subtype.ext
  apply register_operator_ext
  intro a c
  rw [reduced_product_coefficient]
  have he := InfiniteFiniteCorner.matrixOf_ofMatrix (registerBasis (Fin L → A)).orthonormal
    (fun a c => ∏ i, reducedDensityMatrix ψ (a i) (c i))
  have h := congrArg (fun M => M a c) he
  simpa only [InfiniteFiniteCorner.matrixOf, registerBasis_apply, register_inner_single,
    reducedDensityMatrix, matrixTensorPower, InfiniteFiniteCorner.ofMatrix] using h.symm

/-- Trace every purifying-register slot out of the frame-independent physical
Werner output. -/
def reducedWernerOutput {L s : ℕ} (hcard : Fintype.card (A × B) = s + 1)
    (ψ : Register (A × B)) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    TraceClass (Register (Fin L → A)) :=
  partialTraceChannel.toLinearMap
    ((QuantumChannel.ofIsometry (regroup L)).toLinearMap (pureWernerOutput hcard ψ hψ S))

theorem reducedWernerOutput_eq_frame {L s : ℕ} (hcard : Fintype.card (A × B) = s + 1)
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u) (S : Finset (Fin L)) :
    reducedWernerOutput hcard (u 0) (hu.norm_eq_one 0) S =
      (reducedTensorChannel hu L).toLinearMap (wernerOutput (s := s) S) := by
  unfold reducedWernerOutput
  rw [pureWernerOutput_eq_frame hcard hu]
  rfl

theorem environmentRotate_norm (W : Register B →ₗᵢ[ℂ] Register B) (ψ : Register (A × B)) :
    ‖environmentRotate W ψ‖ = ‖ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), environmentRotate_inner,
    ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

/-- Exact cancellation of an arbitrary environment unitary in the original
physical symmetric-sandwich output, with no chosen-frame premise. -/
theorem reducedWernerOutput_environment_invariant {L s : ℕ}
    (hcard : Fintype.card (A × B) = s + 1) (ψ : Register (A × B)) (hψ : ‖ψ‖ = 1)
    (W : Register B →ₗᵢ[ℂ] Register B) (S : Finset (Fin L)) :
    reducedWernerOutput hcard (environmentRotate W ψ) ((environmentRotate_norm W ψ).trans hψ) S =
      reducedWernerOutput hcard ψ hψ S := by
  obtain ⟨u, hu⟩ := exists_purification_frame hcard ψ hψ
  subst ψ
  rw [reducedWernerOutput_eq_frame hcard (environmentRotate_orthonormal u.orthonormal W),
    reducedWernerOutput_eq_frame hcard u.orthonormal]
  exact werner_reduced_environment_invariant u.orthonormal W S

/-- The reduced output of random purification, cloning, and tracing: the
physical Werner formula is evaluated on every randomized purification. -/
def randomizedPurificationOutput {L s : ℕ} (hcard : Fintype.card (A × B) = s + 1)
    (ψ : Register (A × B)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → Register B →ₗᵢ[ℂ] Register B) (S : Finset (Fin L)) :
    TraceClass (Register (Fin L → A)) :=
  ∫ t, reducedWernerOutput hcard (environmentRotate (W t) ψ)
    ((environmentRotate_norm (W t) ψ).trans hψ) S ∂μ

/-- Haar removal is exact for the frame-independent physical output; this
holds for every probability randomization, a stronger statement than Haar. -/
theorem randomizedPurificationOutput_eq {L s : ℕ} (hcard : Fintype.card (A × B) = s + 1)
    (ψ : Register (A × B)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Register B →ₗᵢ[ℂ] Register B) (S : Finset (Fin L)) :
    randomizedPurificationOutput hcard ψ hψ μ W S = reducedWernerOutput hcard ψ hψ S := by
  unfold randomizedPurificationOutput
  have he (t : Ω) := reducedWernerOutput_environment_invariant hcard ψ hψ (W t) S
  simp_rw [he]
  simp

/-- The manuscript's physical PCT-to-Gaussian-mixture step. It starts with the
canonical physical Werner sandwich on randomized purifications, traces all
environment slots, and ends at the actual mixture of reduced tensor powers.
No covariance, frame existence, occupation limit, or integrability premise is
assumed; only the physical dimensions, unit vector, and cloning-ratio limit. -/
theorem randomizedPurification_gaussian_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (hcard : Fintype.card (A × B) = s + 1)
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B)))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Register B →ₗᵢ[ℂ] Register B)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => ‖randomizedPurificationOutput hcard (u 0) (u.orthonormal.norm_eq_one 0)
      μ W (inputSlots n (m n) (hm n)) -
      ∫ z, partialTraceChannel.toLinearMap (vectorProjector
        (regroup (m n) (tensorVector (fun _ : Fin (m n) => frameParticle u z (m n)))))
        ∂MultimodeCoherentGaussianMixture.gaussianProductMeasure
          (fun _ : Fin s => γ - 1)‖) atTop (𝓝 0) := by
  simp only [randomizedPurificationOutput_eq, reducedWernerOutput_eq_frame hcard u.orthonormal]
  exact werner_reduced_gaussian_product_mixture hs u.orthonormal m hm hγ h

/-- The physical randomized PCT output converges in trace norm to the mixture
`∫ ρ_{z,m}^{⊗m} dμ_{γ-1}(z)`, with each `ρ_{z,m}` the actual partial trace of
the normalized one-particle purification. The RHS consists of literal finite
matrix tensor powers, not an assumed identification of limit models. -/
theorem pct_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (hcard : Fintype.card (A × B) = s + 1)
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B)))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Register B →ₗᵢ[ℂ] Register B)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => ‖randomizedPurificationOutput hcard (u 0) (u.orthonormal.norm_eq_one 0)
      μ W (inputSlots n (m n) (hm n)) -
      ∫ z, matrixTensorPower (reducedDensityMatrix (frameParticle u z (m n))) (m n)
        ∂MultimodeCoherentGaussianMixture.gaussianProductMeasure
          (fun _ : Fin s => γ - 1)‖) atTop (𝓝 0) := by
  simpa only [partialTrace_product_eq_matrixTensorPower] using
    randomizedPurification_gaussian_product_mixture hs hcard u μ W m hm hγ h

theorem integrable_reduced_product_mixture {s : ℕ}
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u) (L : ℕ)
    (ν : Measure (Fin s → ℂ)) [IsFiniteMeasure ν] :
    Integrable (fun z => matrixTensorPower (reducedDensityMatrix (frameParticle u z L)) L) ν := by
  have hi := (reducedTensorChannel hu L).toPositiveTracePreservingMap.toContinuousLinearMap.integrable_comp
    (integrable_productProjector L ν)
  change Integrable (fun z => (reducedTensorChannel hu L).toLinearMap
    (vectorProjector (productTensor z L))) ν at hi
  simpa only [reducedTensorChannel_productTensor, partialTrace_product_eq_matrixTensorPower] using hi

/-- Every normalized purification admits the full physical mixture theorem;
the required complete orthonormal frame is produced by the proof. -/
theorem exists_pct_product_mixture {s : ℕ} (hs : 1 ≤ s)
    (hcard : Fintype.card (A × B) = s + 1) (ψ : Register (A × B)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Register B →ₗᵢ[ℂ] Register B)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    ∃ u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × B)), u 0 = ψ ∧
      Tendsto (fun n => ‖randomizedPurificationOutput hcard ψ hψ μ W
        (inputSlots n (m n) (hm n)) -
        ∫ z, matrixTensorPower (reducedDensityMatrix (frameParticle u z (m n))) (m n)
          ∂MultimodeCoherentGaussianMixture.gaussianProductMeasure
            (fun _ : Fin s => γ - 1)‖) atTop (𝓝 0) := by
  obtain ⟨u, hu⟩ := exists_purification_frame hcard ψ hψ
  refine ⟨u, hu, ?_⟩
  have ht := pct_product_mixture hs hcard u μ W m hm hγ h
  simpa only [hu] using ht

end Cloning.PCT
