import Cloning.PCTPartialTrace

/-! Tensor powers of an actual orthonormal purification frame, regrouping of
system and environment slots, and exact reduced-product coefficients. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Topology
open Filter MeasureTheory Cloning.InfiniteTraceClass
namespace Cloning.PCT
open GeneralSymmetricOccupation GeneralCoherent
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {C : Type*} [Fintype C] [DecidableEq C]

def tensorVector {L : ℕ} (v : Fin L → Register C) : Register (Fin L → C) :=
  ⟨fun w => ∏ i, v i (w i), memℓp_gen (by
    simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩

@[simp] theorem tensorVector_apply {L : ℕ} (v : Fin L → Register C) (w : Fin L → C) :
    tensorVector v w = ∏ i, v i (w i) := rfl

theorem tensorVector_inner {L : ℕ} (v w : Fin L → Register C) :
    ⟪tensorVector v, tensorVector w⟫_ℂ = ∏ i, ⟪v i, w i⟫_ℂ := by
  simp only [lp.inner_eq_tsum, tsum_fintype, RCLike.inner_apply, tensorVector_apply,
    map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => w i a * star (v i a))).symm

theorem tensorFrame_orthonormal {d L : ℕ} {u : Fin d → Register C} (hu : Orthonormal ℂ u) :
    Orthonormal ℂ (fun w : Word L d => tensorVector (fun i => u (w i))) := by
  rw [orthonormal_iff_ite]
  intro w v
  rw [tensorVector_inner]
  simp only [orthonormal_iff_ite.mp hu]
  by_cases h : w = v
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ v i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The tensor power of an orthonormal physical one-particle frame. -/
def tensorFrame {d : ℕ} {u : Fin d → Register C} (hu : Orthonormal ℂ u) (L : ℕ) :
    TensorSpace L d →ₗᵢ[ℂ] Register (Fin L → C) :=
  (tensorFrame_orthonormal (L := L) hu).orthogonalFamily.linearIsometry

theorem tensorFrame_apply {d : ℕ} {u : Fin d → Register C} (hu : Orthonormal ℂ u)
    (L : ℕ) (x : TensorSpace L d) (v : Fin L → C) :
    tensorFrame hu L x v = ∑ w : Word L d, x w * ∏ i, u (w i) (v i) := by
  rw [tensorFrame, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp only [LinearIsometry.toSpanSingleton_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, tensorVector_apply]

/-- The normalized one-particle perturbation in the chosen purification frame. -/
def frameParticle {s : ℕ} (u : Fin (s + 1) → Register C) (z : Fin s → ℂ) (L : ℕ) :
    Register C := ∑ j, oneParticle z L j • u j

@[simp] theorem frameParticle_apply {s : ℕ} (u : Fin (s + 1) → Register C)
    (z : Fin s → ℂ) (L : ℕ) (c : C) :
    frameParticle u z L c = ∑ j, oneParticle z L j * u j c := by
  simp only [frameParticle, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]

theorem tensorFrame_productTensor {s : ℕ} {u : Fin (s + 1) → Register C}
    (hu : Orthonormal ℂ u) (z : Fin s → ℂ) (L : ℕ) :
    tensorFrame hu L (productTensor z L) = tensorVector (fun _ : Fin L => frameParticle u z L) := by
  ext v
  simp only [tensorFrame_apply, productTensor_apply, tensorVector_apply,
    frameParticle_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => oneParticle z L j * u j (v i))).symm

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def pairWordsEquiv (L : ℕ) : (Fin L → A × B) ≃ ((Fin L → A) × (Fin L → B)) where
  toFun w := (fun i => (w i).1, fun i => (w i).2)
  invFun w := fun i => (w.1 i, w.2 i)
  left_inv w := by funext i; exact Prod.eta (w i)
  right_inv w := by cases w; rfl

theorem regroup_orthonormal (L : ℕ) :
    Orthonormal ℂ (fun w : Fin L → A × B =>
      (lp.single 2 (pairWordsEquiv L w) 1 : Register ((Fin L → A) × (Fin L → B)))) := by
  rw [orthonormal_iff_ite]
  intro w v
  simp only [register_inner_single, lp.single_apply, Pi.single_apply]
  simp only [(pairWordsEquiv L).injective.eq_iff]

def regroup (L : ℕ) : Register (Fin L → A × B) →ₗᵢ[ℂ]
    Register ((Fin L → A) × (Fin L → B)) :=
  (regroup_orthonormal (A := A) (B := B) L).orthogonalFamily.linearIsometry

@[simp] theorem regroup_apply (L : ℕ) (x : Register (Fin L → A × B))
    (a : Fin L → A) (b : Fin L → B) :
    regroup L x (a, b) = x (fun i => (a i, b i)) := by
  classical
  rw [regroup, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  simp only [LinearIsometry.toSpanSingleton_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  have he (w : Fin L → A × B) : (a, b) = pairWordsEquiv L w ↔ w = (fun i => (a i, b i)) := by
    constructor
    · intro h
      exact (congrArg (pairWordsEquiv (A := A) (B := B) L).symm h).symm
    · intro h
      subst w
      rfl
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Trace out all environment slots after the actual tensor-power change of
one-particle frame. -/
def reducedTensorChannel {s : ℕ} {u : Fin (s + 1) → Register (A × B)}
    (hu : Orthonormal ℂ u) (L : ℕ) :
    QuantumChannel (TensorSpace L (s + 1)) (Register (Fin L → A)) :=
  partialTraceChannel.comp
    ((QuantumChannel.ofIsometry (regroup (A := A) (B := B) L)).comp
      (QuantumChannel.ofIsometry (tensorFrame hu L)))

theorem reducedTensorChannel_productTensor {s : ℕ} {u : Fin (s + 1) → Register (A × B)}
    (hu : Orthonormal ℂ u) (z : Fin s → ℂ) (L : ℕ) :
    (reducedTensorChannel hu L).toLinearMap (vectorProjector (productTensor z L)) =
      partialTraceChannel.toLinearMap (vectorProjector
        (regroup L (tensorVector (fun _ : Fin L => frameParticle u z L)))) := by
  change partialTraceChannel.toLinearMap ((QuantumChannel.ofIsometry (regroup L)).toLinearMap
    ((QuantumChannel.ofIsometry (tensorFrame hu L)).toLinearMap
      (vectorProjector (productTensor z L)))) = _
  rw [QuantumChannel.ofIsometry_vectorProjector, tensorFrame_productTensor,
    QuantumChannel.ofIsometry_vectorProjector]

/-- Partial trace of a tensor power is exactly the tensor power of the reduced
one-particle matrix. This identifies every coefficient of the physical product
state inside the PCT Gaussian mixture. -/
theorem reduced_product_coefficient (v : Register (A × B)) (L : ℕ)
    (a c : Fin L → A) :
    (partialTraceChannel.toLinearMap (vectorProjector
      (regroup L (tensorVector (fun _ : Fin L => v))))).1 (lp.single 2 c 1) a =
      ∏ i, ∑ b : B, v (a i, b) * star (v (c i, b)) := by
  rw [show partialTraceChannel.toLinearMap = partialTraceLinear by rfl,
    partialTraceLinear_coefficient]
  simp only [vectorProjector, TraceClass.ofOperator_coe, InnerProductSpace.rankOne_apply,
    lp.inner_single_right, RCLike.inner_apply, one_mul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, regroup_apply, tensorVector_apply, map_prod, ← Finset.prod_mul_distrib]
  simpa only [mul_comm] using
    (Fintype.prod_sum (fun i b => star (v (c i, b)) * v (a i, b))).symm

/-- In any actual orthonormal purification frame, the physical Werner output
after tracing out every environment slot converges to the Gaussian mixture
of reduced product states. No partial-trace or integration hypothesis remains. -/
theorem werner_reduced_gaussian_product_mixture {s : ℕ} (hs : 1 ≤ s)
    {u : Fin (s + 1) → Register (A × B)} (hu : Orthonormal ℂ u)
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) {γ : ℝ} (hγ : 1 < γ)
    (h : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => ‖(reducedTensorChannel hu (m n)).toLinearMap
      (wernerOutput (s := s) (inputSlots n (m n) (hm n))) -
      ∫ z, partialTraceChannel.toLinearMap (vectorProjector
        (regroup (m n) (tensorVector (fun _ : Fin (m n) => frameParticle u z (m n)))))
        ∂MultimodeCoherentGaussianMixture.gaussianProductMeasure
          (fun _ : Fin s => γ - 1)‖) atTop (𝓝 0) := by
  simpa only [reducedTensorChannel_productTensor] using
    physical_werner_gaussian_mixture_after_channels hs m hm hγ h
      (fun n => reducedTensorChannel hu (m n))

end Cloning.PCT
