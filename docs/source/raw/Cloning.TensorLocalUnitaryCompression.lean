import Cloning.TensorLocalUnitaryFrameMatrix
import Mathlib.Topology.Instances.Matrix

/-! Exact finite-matrix formulas for physical generator polynomials on a fixed
cutoff. The ambient generator need not preserve the entire cutoff: only the
finitely many powers under consideration must lie inside it. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.TensorLocalUnitary
open Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

section Compression
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [Fintype I] [DecidableEq I]
    (K : Submodule ℂ H) (b : OrthonormalBasis I ℂ K) (A : H →L[ℂ] H)

def ambientMatrix : Matrix I I ℂ := fun i j => ⟪(b i : H), A (b j : H)⟫_ℂ

theorem inner_map_eq_sum {x : H} (hx : x ∈ K) (i : I) :
    ⟪(b i : H), A x⟫_ℂ =
      ∑ j, ambientMatrix K b A i j * ⟪(b j : H), x⟫_ℂ := by
  have he : (∑ j, ⟪(b j : H), x⟫_ℂ • (b j : H)) = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg (fun v : K => (v : H)) (b.sum_repr' ⟨x,hx⟩)
  conv_lhs => rw [← he]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, ambientMatrix]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Compression gives the exact polynomial action whenever all required
intermediate physical vectors stay in the cutoff. -/
theorem inner_pow_eq_mulVec (x : H) (m : ℕ)
    (hmem : ∀ r < m, (A^r) x ∈ K) (i : I) :
    ⟪(b i : H), (A^m) x⟫_ℂ =
      ((ambientMatrix K b A)^m).mulVec (fun j => ⟪(b j : H), x⟫_ℂ) i := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, inner_map_eq_sum K b A (hmem m (by omega))]
    simp_rw [ih (fun r hr => hmem r (by omega))]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rfl

end Compression

variable {d : ℕ}

def physicalCutoffMatrix (mu : Fin d → ℕ) (hmu : Antitone mu) (R : ℕ)
    (z : PositiveRoot d → ℂ) : Matrix (CutoffIndex d R) (CutoffIndex d R) ℂ :=
  fun i j => ⟪cutoffFrame (partitionHighestTensor mu hmu) mu R i,
    rootGenerator mu z (cutoffFrame (partitionHighestTensor mu hmu) mu R j)⟫_ℂ

def oscillatorCutoffMatrix (R : ℕ) (z : PositiveRoot d → ℂ) :
    Matrix (CutoffIndex d R) (CutoffIndex d R) ℂ :=
  fun i j => oscillatorEntry z (cutoffWord d R i) (cutoffWord d R j)

/-- The entire finite physical generator matrix converges, not merely a
selection of its scalar entries. -/
theorem physicalCutoffMatrix_tendsto
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀)) (R : ℕ) :
    Tendsto (fun N => physicalCutoffMatrix (mu N) (hmu N) R (z N))
      atTop (𝓝 (oscillatorCutoffMatrix R z₀)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact partition_rootGenerator_frame_tendsto mu hmu δ hδ hgap z z₀ hz R i j

/-- Every fixed-degree matrix polynomial has its actual oscillator limit. -/
theorem physicalCutoffMatrix_pow_tendsto
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d, δ N ≤ rootGap (mu N) a)
    (z : ℕ → PositiveRoot d → ℂ) (z₀ : PositiveRoot d → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀)) (R m : ℕ) :
    Tendsto (fun N => physicalCutoffMatrix (mu N) (hmu N) R (z N)^m)
      atTop (𝓝 ((oscillatorCutoffMatrix R z₀)^m)) :=
  (physicalCutoffMatrix_tendsto mu hmu δ hδ hgap z z₀ hz R).pow m

end Cloning.TensorLocalUnitary
