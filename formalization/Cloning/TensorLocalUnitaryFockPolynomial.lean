import Cloning.TensorLocalUnitaryPolynomial
import Cloning.TensorLANEmbeddingPhysical

/-! Concrete transport of physical generator polynomials into the actual
occupation-number Fock space. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Explicit vector formula for the already-constructed finite-frame transport. -/
theorem frameTransport_apply_sum {H K I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Fintype I] (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (b : OrthonormalBasis I ℂ S) (f : I → K) (hf : Orthonormal ℂ f) (x : H) :
    frameTransport S b f hf x = ∑ i, ⟪(b i : H), x⟫_ℂ • f i := by
  change basisFrameIsometry S b f hf (S.orthogonalProjection x) = _
  rw [← b.sum_repr' (S.orthogonalProjection x)]
  simp only [map_sum, map_smul, basisFrameIsometry_basis,
    S.inner_orthogonalProjection_eq_of_mem_left]

variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite


/-- The common-frame coordinate map on the full physical tensor register.
On the proved admissible tail it is exactly a contraction/partial isometry. -/
def cutoffEmbedding (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (Q : ℕ) :
    TensorRegister n (Fin d) →L[ℂ] RootFock d :=
  ∑ i : CutoffIndex d Q,
    (innerSL ℂ (cutoffFrame Ω mu Q i)).smulRight (cutoffNumberFrame d Q i)

@[simp] theorem cutoffEmbedding_apply (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (Q : ℕ) (x : TensorRegister n (Fin d)) :
    cutoffEmbedding Ω mu Q x = ∑ i, ⟪cutoffFrame Ω mu Q i, x⟫_ℂ • cutoffNumberFrame d Q i := by
  simp only [cutoffEmbedding, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply]

theorem cutoffEmbedding_eq_frameTransport (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (Q : ℕ) (b : OrthonormalBasis (CutoffIndex d Q) ℂ (cyclicCutoff Ω (Q : ℤ)))
    (hb : ∀ i, (b i : TensorRegister n (Fin d)) = cutoffFrame Ω mu Q i) :
    cutoffEmbedding Ω mu Q = frameTransport (cyclicCutoff Ω (Q : ℤ)) b
      (cutoffNumberFrame d Q) (cutoffNumberFrame_orthonormal d Q) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cutoffEmbedding_apply, frameTransport_apply_sum, hb]

variable (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
include hδ hgap

theorem cutoffEmbedding_eventually_contraction (Q : ℕ) :
    ∀ᶠ N in atTop, ∀ x, ‖cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q x‖ ≤ ‖x‖ := by
  filter_upwards [partition_eventually_cutoffOrthonormalBasis mu hmu δ hδ hgap Q] with N hb
  obtain ⟨b,hb⟩ := hb
  rw [cutoffEmbedding_eq_frameTransport _ _ Q b hb]
  exact frameTransport_contraction _ _ _ _

/-- Physical finite generator powers converge in the norm of the actual
infinite Fock Hilbert space, under the concrete common-frame transport. -/
theorem cutoffEmbedding_power_tendsto (z : ℕ → PositiveRoot d → ℂ)
    (z₀ : PositiveRoot d → ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (R Q m : ℕ) (hQ : R+m*d ≤ Q) (w : List (PositiveRoot d))
    (hw : loweringHeight w ≤ R) :
    Tendsto (fun N => cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
      ((rootGenerator (n := ∑ j, mu N j) (mu N) (z N)^m)
        (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w)))
      atTop (𝓝 (∑ i, (((oscillatorCutoffMatrix Q z₀)^m).mulVec
        (limitingWordCoordinates Q w) i) • cutoffNumberFrame d Q i)) := by
  simp only [cutoffEmbedding_apply]
  apply tendsto_finset_sum
  intro i _
  exact (physical_word_power_tendsto mu hmu δ hδ hgap z z₀ hz R Q m hQ w hw i).smul_const _

/-- Finite Taylor polynomials of the literal physical unitary converge in Fock
norm, for the actual input normalized PBW word. -/
theorem cutoffEmbedding_taylor_tendsto (z : ℕ → PositiveRoot d → ℂ)
    (z₀ : PositiveRoot d → ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (R Q m : ℕ) (hQ : R+m*d ≤ Q) (w : List (PositiveRoot d))
    (hw : loweringHeight w ≤ R) :
    Tendsto (fun N => cutoffEmbedding (partitionHighestTensor (mu N) (hmu N)) (mu N) Q
      (∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) •
        ((rootGenerator (n := ∑ k, mu N k) (mu N) (z N)^j)
          (normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N) w))))
      atTop (𝓝 (∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) •
        (∑ i, (((oscillatorCutoffMatrix Q z₀)^j).mulVec
          (limitingWordCoordinates Q w) i) • cutoffNumberFrame d Q i))) := by
  simp only [map_sum, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  apply tendsto_finset_sum
  intro j hj
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  exact (cutoffEmbedding_power_tendsto mu hmu δ hδ hgap z z₀ hz R Q j
    ((Nat.add_le_add_left (Nat.mul_le_mul_right d hjm) R).trans hQ) w hw).const_smul _

end Cloning.TensorLocalUnitary
