import Cloning.MatrixFidelityLifted
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Order.Field

/-!
# A concrete matrix version of the lifted convergence step

Label sets and sector dimensions may grow with the sample size. The remaining
inputs are the sector approximation and the classical affinity limit. There is
no assumed direct-sum identity, tensor identity, or quantum continuity estimate.
This theorem applies when every positive-weight sector satisfies the estimate;
it does not handle deletion of overlapping contributions within a sector.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker Topology
open Filter

namespace Cloning.MatrixFidelity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem weighted_lifted_fidelity_converges
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    {d s : (n : ℕ) → I n → Type*}
    [∀ n i, Fintype (d n i)] [∀ n i, DecidableEq (d n i)]
    [∀ n i, Fintype (s n i)] [∀ n i, DecidableEq (s n i)]
    (σ ρ : (n : ℕ) → (i : I n) → State (d n i))
    (τ : (n : ℕ) → (i : I n) → State (s n i))
    (p q : (n : ℕ) → I n → ℝ) (η : ℕ → ℝ) (c l : ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ n i, 0 ≤ q n i)
    (hps : ∀ n, ∑ i, p n i ≤ 1) (hqs : ∀ n, ∑ i, q n i ≤ 1)
    (hη : ∀ n, 0 ≤ η n)
    (hsector : ∀ n i, 0 < q n i →
      |fidelity (σ n i).matrix (ρ n i).matrix - c| ≤ η n)
    (hηlimit : Tendsto η atTop (𝓝 0))
    (hlabel : Tendsto (fun n => Cloning.BlockFidelity.classicalAffinity (q n) (p n))
      atTop (𝓝 l)) :
    Tendsto (fun n =>
      fidelity (Matrix.blockDiagonal' (fun i => (q n i • (σ n i).matrix) ⊗ₖ (τ n i).matrix))
        (Matrix.blockDiagonal' (fun i => (p n i • (ρ n i).matrix) ⊗ₖ (τ n i).matrix)))
      atTop (𝓝 (c * l)) := by
  let actual := fun n =>
    fidelity (Matrix.blockDiagonal' (fun i => (q n i • (σ n i).matrix) ⊗ₖ (τ n i).matrix))
      (Matrix.blockDiagonal' (fun i => (p n i • (ρ n i).matrix) ⊗ₖ (τ n i).matrix))
  have herr : ∀ n, |actual n - c * Cloning.BlockFidelity.classicalAffinity (q n) (p n)|
      ≤ η n := by
    intro n
    apply fidelity_weighted_lifted_blocks_error
      (fun i => (σ n i).matrix) (fun i => (ρ n i).matrix) (fun i => (τ n i).matrix)
      (p n) (q n) c (η n)
      (fun i => (σ n i).positive) (fun i => (ρ n i).positive)
      (fun i => (τ n i).positive) (hp n) (hq n)
      (fun i => by rw [(τ n i).trace_one]; rfl) (hps n) (hqs n) (hη n) (hsector n)
  have hdiff : Tendsto
      (fun n => actual n - c * Cloning.BlockFidelity.classicalAffinity (q n) (p n))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hηlimit.eventually_lt_const hε] with n hn
    simpa only [Real.dist_eq, sub_zero] using (herr n).trans_lt hn
  have htotal := hdiff.add (hlabel.const_mul c)
  simpa only [sub_add_cancel, zero_add] using htotal

end Cloning.MatrixFidelity
