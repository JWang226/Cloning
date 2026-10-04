import Cloning.Main
import Cloning.MatrixFidelityDeletion
import Cloning.MatrixFidelityAchievability

/-!
# Lifted matrix fidelity with overlapping positive deletion

The quantum deletion estimate is proved from concrete matrix inequalities in
`MatrixFidelityDeletion`. Thus neither theorem below takes `hquantum` as an
assumption. The sector approximation, discarded-mass estimate, and classical
label limit are the remaining asymptotic inputs.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker Topology
open Filter Matrix

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The paper's finite `η + 2√ε` estimate for actual positive matrix blocks.
Retained and discarded contributions may have overlapping support. -/
theorem lifted_matrix_factorization_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d s : ι → Type*}
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (X G : ∀ i, Matrix (d i) (d i) ℂ)
    (ρ : ∀ i, State (d i)) (τ : ∀ i, State (s i))
    (p : ι → ℝ) (c η : ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hG : ∀ i, (G i).PosSemidef)
    (hdiff : ∀ i, (X i - G i).PosSemidef)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hXmass : ∑ i, (Matrix.trace (X i)).re ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : 0 ≤ η)
    (hsector : ∀ i, 0 < (Matrix.trace (G i)).re →
      |fidelity (normalizedBlock (G i)) (ρ i).matrix - c| ≤ η) :
    |fidelity (Matrix.blockDiagonal' (fun i => X i ⊗ₖ (τ i).matrix))
        (Matrix.blockDiagonal' (fun i => (p i • (ρ i).matrix) ⊗ₖ (τ i).matrix)) -
      c * Cloning.BlockFidelity.classicalAffinity
        (fun i => (Matrix.trace (X i)).re) p| ≤
      η + 2 * Real.sqrt (∑ i, ((Matrix.trace (X i)).re - (Matrix.trace (G i)).re)) := by
  apply Cloning.BlockFidelity.lifted_factorization_bound p
    (fun i => (Matrix.trace (X i)).re) (fun i => (Matrix.trace (G i)).re)
    (fun i => fidelity (normalizedBlock (G i)) (ρ i).matrix)
    _ c η hp (fun i => trace_re_nonneg (hG i))
    (fun i => trace_re_mono (show G i ≤ X i from hdiff i))
    hpsum hXmass hc0 hc1 hη hsector
  exact lifted_deletion_bound X G (fun i => (ρ i).matrix) (fun i => (τ i).matrix) p
    hX hG (fun i => (ρ i).positive) (fun i => (τ i).positive) hp hdiff
    (fun i => by rw [(ρ i).trace_one]; rfl)
    (fun i => by rw [(τ i).trace_one]; rfl) hpsum

/-- Concrete growing-dimension version of the manuscript's lifted convergence
argument. There is no assumed quantum continuity or block-fidelity identity. -/
theorem lifted_matrix_fidelity_converges
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    {d s : (n : ℕ) → I n → Type*}
    [∀ n i, Fintype (d n i)] [∀ n i, DecidableEq (d n i)]
    [∀ n i, Fintype (s n i)] [∀ n i, DecidableEq (s n i)]
    (X G : (n : ℕ) → (i : I n) → Matrix (d n i) (d n i) ℂ)
    (ρ : (n : ℕ) → (i : I n) → State (d n i))
    (τ : (n : ℕ) → (i : I n) → State (s n i))
    (p : (n : ℕ) → I n → ℝ) (η : ℕ → ℝ) (c l : ℝ)
    (hX : ∀ n i, (X n i).PosSemidef) (hG : ∀ n i, (G n i).PosSemidef)
    (hdiff : ∀ n i, (X n i - G n i).PosSemidef)
    (hp : ∀ n i, 0 ≤ p n i) (hpsum : ∀ n, ∑ i, p n i = 1)
    (hXmass : ∀ n, ∑ i, (Matrix.trace (X n i)).re ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : ∀ n, 0 ≤ η n)
    (hsector : ∀ n i, 0 < (Matrix.trace (G n i)).re →
      |fidelity (normalizedBlock (G n i)) (ρ n i).matrix - c| ≤ η n)
    (hηlimit : Tendsto η atTop (𝓝 0))
    (hmass : Tendsto (fun n => ∑ i,
      ((Matrix.trace (X n i)).re - (Matrix.trace (G n i)).re)) atTop (𝓝 0))
    (hlabel : Tendsto (fun n => Cloning.BlockFidelity.classicalAffinity
      (fun i => (Matrix.trace (X n i)).re) (p n)) atTop (𝓝 l)) :
    Tendsto (fun n =>
      fidelity (Matrix.blockDiagonal' (fun i => X n i ⊗ₖ (τ n i).matrix))
        (Matrix.blockDiagonal' (fun i => (p n i • (ρ n i).matrix) ⊗ₖ (τ n i).matrix)))
      atTop (𝓝 (c * l)) := by
  apply Cloning.lifted_fidelity_converges p
    (fun n i => (Matrix.trace (X n i)).re) (fun n i => (Matrix.trace (G n i)).re)
    (fun n i => fidelity (normalizedBlock (G n i)) (ρ n i).matrix)
    _ η c l hp (fun n i => trace_re_nonneg (hG n i))
    (fun n i => trace_re_mono (show G n i ≤ X n i from hdiff n i))
    hpsum hXmass hc0 hc1 hη hsector _ hηlimit hmass hlabel
  intro n
  exact lifted_deletion_bound (X n) (G n) (fun i => (ρ n i).matrix)
    (fun i => (τ n i).matrix) (p n) (hX n) (hG n)
    (fun i => (ρ n i).positive) (fun i => (τ n i).positive) (hp n) (hdiff n)
    (fun i => by rw [(ρ n i).trace_one]; rfl)
    (fun i => by rw [(τ n i).trace_one]; rfl) (hpsum n)

/-- Achievability needs only lower sector bounds. This conclusion deliberately
does not assert an upper bound or exact convergence of mixture fidelities. -/
theorem lifted_matrix_eventual_achievability
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    {d s : (n : ℕ) → I n → Type*}
    [∀ n i, Fintype (d n i)] [∀ n i, DecidableEq (d n i)]
    [∀ n i, Fintype (s n i)] [∀ n i, DecidableEq (s n i)]
    (X G : (n : ℕ) → (i : I n) → Matrix (d n i) (d n i) ℂ)
    (ρ : (n : ℕ) → (i : I n) → State (d n i))
    (τ : (n : ℕ) → (i : I n) → State (s n i))
    (p : (n : ℕ) → I n → ℝ) (η : ℕ → ℝ) (c l : ℝ)
    (hX : ∀ n i, (X n i).PosSemidef) (hG : ∀ n i, (G n i).PosSemidef)
    (hdiff : ∀ n i, (X n i - G n i).PosSemidef)
    (hp : ∀ n i, 0 ≤ p n i) (hpsum : ∀ n, ∑ i, p n i = 1)
    (hXmass : ∀ n, ∑ i, (Matrix.trace (X n i)).re ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hη : ∀ n, 0 ≤ η n)
    (hsectorLower : ∀ n i, 0 < (Matrix.trace (G n i)).re →
      c - η n ≤ fidelity (normalizedBlock (G n i)) (ρ n i).matrix)
    (hηlimit : Tendsto η atTop (𝓝 0))
    (hmass : Tendsto (fun n => ∑ i,
      ((Matrix.trace (X n i)).re - (Matrix.trace (G n i)).re)) atTop (𝓝 0))
    (hlabel : Tendsto (fun n => Cloning.BlockFidelity.classicalAffinity
      (fun i => (Matrix.trace (X n i)).re) (p n)) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, c * l - ε <
      fidelity (Matrix.blockDiagonal' (fun i => X n i ⊗ₖ (τ n i).matrix))
        (Matrix.blockDiagonal' (fun i => (p n i • (ρ n i).matrix) ⊗ₖ (τ n i).matrix)) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (∑ i,
      ((Matrix.trace (X n i)).re - (Matrix.trace (G n i)).re))) atTop (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hmass
  have hlower : Tendsto (fun n => c * Cloning.BlockFidelity.classicalAffinity
      (fun i => (Matrix.trace (X n i)).re) (p n) - η n -
      Real.sqrt (∑ i, ((Matrix.trace (X n i)).re - (Matrix.trace (G n i)).re)))
      atTop (𝓝 (c * l)) := by
    simpa using ((hlabel.const_mul c).sub hηlimit).sub hsqrt
  intro ε hε
  have hgap : c * l - ε < c * l := sub_lt_self _ hε
  filter_upwards [hlower.eventually_const_lt hgap] with n hn
  apply hn.trans_le
  exact fidelity_lifted_achievability (X n) (G n) (fun i => (ρ n i).matrix)
    (fun i => (τ n i).matrix) (p n) c (η n) (hX n) (hG n)
    (fun i => (ρ n i).positive) (fun i => (τ n i).positive) (hp n)
    (fun i => by rw [(τ n i).trace_one]; rfl) (hpsum n) (hXmass n)
    (fun i => show G n i ≤ X n i from hdiff n i) hc0 hc1 (hη n) (hsectorLower n)

end Cloning.MatrixFidelity
