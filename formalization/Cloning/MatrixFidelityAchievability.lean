import Cloning.MatrixFidelityLifted
import Cloning.MatrixFidelityProjector
import Mathlib.Tactic.Linarith

/-!
# Concrete finite-block achievability from one-sided sector bounds

The lower bound uses monotonicity under deletion and classical affinity
continuity. It requires only lower fidelity bounds for the normalized retained
sectors, not two-sided convergence of mixture fidelities.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false

/-- A one-sided sector estimate passes through subprobability Hellinger weights. -/
lemma weighted_sector_lower_bound {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ) (c η : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i ≤ 1) (hqs : ∑ i, q i ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ i, 0 < q i → c - η ≤ f i) :
    c * Cloning.BlockFidelity.classicalAffinity q p - η ≤
      ∑ i, Real.sqrt (q i) * Real.sqrt (p i) * f i := by
  have hsum : ∑ i, Real.sqrt (q i) * Real.sqrt (p i) * (c - η) ≤
      ∑ i, Real.sqrt (q i) * Real.sqrt (p i) * f i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hpos : 0 < q i
    · exact mul_le_mul_of_nonneg_left (hsector i hpos)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · have hz : q i = 0 := le_antisymm (le_of_not_gt hpos) (hq i)
      simp [hz]
  have heq : ∑ i, Real.sqrt (q i) * Real.sqrt (p i) * (c - η) =
      c * Cloning.BlockFidelity.classicalAffinity q p -
        η * Cloning.BlockFidelity.classicalAffinity q p := by
    rw [← Finset.sum_mul]
    unfold Cloning.BlockFidelity.classicalAffinity
    ring
  have herror : η * Cloning.BlockFidelity.classicalAffinity q p ≤ η := by
    simpa using mul_le_mul_of_nonneg_left
      (Cloning.BlockFidelity.classicalAffinity_le_one q p hq hp hqs hps) hη
  rw [heq] at hsum
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d s : ι → Type*}
variable [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
variable [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]

/-- A finite achievability estimate for actual lifted matrix blocks. The output
marginal is the actual block trace, and only retained positive-trace sectors
need satisfy the lower fidelity estimate. -/
theorem fidelity_lifted_achievability
    (X G ρ : ∀ i, Matrix (d i) (d i) ℂ)
    (τ : ∀ i, Matrix (s i) (s i) ℂ) (p : ι → ℝ) (c η : ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hG : ∀ i, (G i).PosSemidef)
    (hρ : ∀ i, (ρ i).PosSemidef) (hτ : ∀ i, (τ i).PosSemidef)
    (hp : ∀ i, 0 ≤ p i) (htrace : ∀ i, (Matrix.trace (τ i)).re = 1)
    (hps : ∑ i, p i = 1) (hXs : ∑ i, (Matrix.trace (X i)).re ≤ 1)
    (hGX : ∀ i, G i ≤ X i) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hsectorLower : ∀ i, 0 < (Matrix.trace (G i)).re →
      c - η ≤ fidelity (normalizedBlock (G i)) (ρ i)) :
    c * Cloning.BlockFidelity.classicalAffinity
      (fun i => (Matrix.trace (X i)).re) p - η -
      Real.sqrt (∑ i, ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re)) ≤
      fidelity (Matrix.blockDiagonal' (fun i => X i ⊗ₖ τ i))
        (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) := by
  let q : ι → ℝ := fun i => (Matrix.trace (X i)).re
  let qG : ι → ℝ := fun i => (Matrix.trace (G i)).re
  have hqG : ∀ i, 0 ≤ qG i := fun i => trace_re_nonneg (hG i)
  have hqGX : ∀ i, qG i ≤ q i := fun i => trace_re_mono (hGX i)
  have hqGs : ∑ i, qG i ≤ 1 := (Finset.sum_le_sum fun i _ => hqGX i).trans hXs
  have hretained : c * Cloning.BlockFidelity.classicalAffinity qG p - η ≤
      fidelity (Matrix.blockDiagonal' (fun i => G i ⊗ₖ τ i))
        (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) := by
    rw [fidelity_lifted_blocks_normalized G ρ τ p hG hρ hτ hp htrace]
    exact weighted_sector_lower_bound p qG
      (fun i => fidelity (normalizedBlock (G i)) (ρ i)) c η hp hqG
      (le_of_eq hps) hqGs hη hsectorLower
  have hmono : fidelity (Matrix.blockDiagonal' (fun i => G i ⊗ₖ τ i))
      (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) ≤
      fidelity (Matrix.blockDiagonal' (fun i => X i ⊗ₖ τ i))
        (Matrix.blockDiagonal' (fun i => (p i • ρ i) ⊗ₖ τ i)) := by
    rw [fidelity_lifted_blocks G ρ τ p hG hρ hτ hp htrace,
      fidelity_lifted_blocks X ρ τ p hX hρ hτ hp htrace]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (fidelity_mono_left (hGX i) (ρ i)) (Real.sqrt_nonneg _)
  have htrim := Cloning.BlockFidelity.classicalAffinity_trim_bound q qG p hqG hp hqGX hps
  have hdiff : Cloning.BlockFidelity.classicalAffinity q p -
      Cloning.BlockFidelity.classicalAffinity qG p ≤ Real.sqrt (∑ i, (q i - qG i)) :=
    (le_abs_self _).trans htrim
  have hscaled : c * (Cloning.BlockFidelity.classicalAffinity q p -
      Cloning.BlockFidelity.classicalAffinity qG p) ≤ Real.sqrt (∑ i, (q i - qG i)) := by
    calc
      _ ≤ c * Real.sqrt (∑ i, (q i - qG i)) := mul_le_mul_of_nonneg_left hdiff hc0
      _ ≤ _ := by
        simpa using (mul_le_mul_of_nonneg_right hc1
          (Real.sqrt_nonneg (∑ i, (q i - qG i))))
  change c * Cloning.BlockFidelity.classicalAffinity q p - η -
    Real.sqrt (∑ i, (q i - qG i)) ≤ _
  linarith

end Cloning.MatrixFidelity
