import Cloning.MatrixLiftedChannel

/-!
# A genuine channel for finite sector transitions

The map is defined on every complex matrix. It measures the sector, discards
its input multiplicity, applies an arbitrary completely positive sector map,
samples the output sector, and prepares the normalized output multiplicity.
Complete positivity is proved at every ancilla dimension directly from that
of the sector maps; no Kraus representation hypothesis is imposed.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix Cloning.Channels Cloning.MatrixFidelity

namespace Cloning.MatrixLiftedCPTP

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
variable {α χ : μ → Type*} {β κ : ν → Type*}
variable [∀ i, Fintype (α i)] [∀ i, Fintype (χ i)]
variable [∀ j, Fintype (β j)] [∀ j, Fintype (κ j)]
variable [∀ i, DecidableEq (α i)] [∀ i, DecidableEq (χ i)]
variable [∀ j, DecidableEq (β j)] [∀ j, DecidableEq (κ j)]

/-- The unnormalized conditional input, after discarding multiplicity. -/
def inputReduction (i : μ) (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    Matrix (α i) (α i) ℂ :=
  ∑ t : χ i, X.submatrix (fun a => ⟨i, (a, t)⟩) (fun a => ⟨i, (a, t)⟩)

theorem inputReduction_add (i : μ)
    (X Y : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    inputReduction i (X + Y) = inputReduction i X + inputReduction i Y := by
  ext a b
  simp [inputReduction, Matrix.sum_apply, Finset.sum_add_distrib]

theorem inputReduction_smul (i : μ) (c : ℂ)
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    inputReduction i (c • X) = c • inputReduction i X := by
  ext a b
  simp [inputReduction, Matrix.sum_apply, Finset.mul_sum]

theorem inputReduction_trace_sum
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    (∑ i, Matrix.trace (inputReduction i X)) = Matrix.trace X := by
  simp [inputReduction, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Fintype.sum_sigma, Fintype.sum_prod_type]

theorem inputReduction_completely_positive (i : μ) (k : ℕ)
    (X : Matrix (Fin k × (Σ i, α i × χ i)) (Fin k × (Σ i, α i × χ i)) ℂ)
    (hX : X.PosSemidef) : (amplify (inputReduction i) X).PosSemidef := by
  have heq : amplify (inputReduction i) X =
      ∑ t : χ i, X.submatrix (fun a : Fin k × α i => (a.1, ⟨i, (a.2, t)⟩))
        (fun a : Fin k × α i => (a.1, ⟨i, (a.2, t)⟩)) := by
    ext a b
    simp [amplify, inputReduction, Matrix.sum_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun t _ => hX.submatrix _)

/-- The unnormalized output block, for arbitrary complex inputs. -/
def outputBlock (Φ : ∀ i j, MatrixChannel (α i) (β j)) (K : μ → ν → ℝ)
    (j : ν) (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    Matrix (β j) (β j) ℂ :=
  ∑ i, K i j • (Φ i j).toFun (inputReduction i X)

theorem outputBlock_add (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (j : ν)
    (X Y : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    outputBlock Φ K j (X + Y) = outputBlock Φ K j X + outputBlock Φ K j Y := by
  simp [outputBlock, inputReduction_add, MatrixChannel.map_add, smul_add,
    Finset.sum_add_distrib]

theorem outputBlock_smul (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (j : ν) (c : ℂ)
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    outputBlock Φ K j (c • X) = c • outputBlock Φ K j X := by
  simp [outputBlock, inputReduction_smul, MatrixChannel.map_smul,
    smul_comm (K _ _) c, Finset.smul_sum]

theorem outputBlock_trace (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (j : ν)
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    Matrix.trace (outputBlock Φ K j X) =
      ∑ i, (K i j : ℂ) * Matrix.trace (inputReduction i X) := by
  simp [outputBlock, Matrix.trace_sum, MatrixChannel.trace_preserving,
    Complex.real_smul]

theorem outputBlock_completely_positive (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j) (j : ν) (k : ℕ)
    (X : Matrix (Fin k × (Σ i, α i × χ i)) (Fin k × (Σ i, α i × χ i)) ℂ)
    (hX : X.PosSemidef) : (amplify (outputBlock Φ K j) X).PosSemidef := by
  have heq : amplify (outputBlock Φ K j) X =
      ∑ i, K i j • amplify (Φ i j).toFun (amplify (inputReduction i) X) := by
    ext a b
    simp [amplify, outputBlock, Matrix.sum_apply]
  rw [heq]
  apply Matrix.posSemidef_sum
  intro i _
  exact ((Φ i j).completely_positive k _
    (inputReduction_completely_positive i k X hX)).smul (hK i j)

/-- Measure, discard, transition, and prepare, on the full matrix algebra. -/
def channelMap (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (τ : ∀ j, State (κ j))
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    Matrix (Σ j, β j × κ j) (Σ j, β j × κ j) ℂ :=
  Matrix.blockDiagonal' (fun j => outputBlock Φ K j X ⊗ₖ (τ j).matrix)

theorem channelMap_add (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (τ : ∀ j, State (κ j))
    (X Y : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    channelMap Φ K τ (X + Y) = channelMap Φ K τ X + channelMap Φ K τ Y := by
  simp only [channelMap, outputBlock_add, Matrix.add_kronecker]
  exact Matrix.blockDiagonal'_add _ _

theorem channelMap_smul (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (τ : ∀ j, State (κ j)) (c : ℂ)
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    channelMap Φ K τ (c • X) = c • channelMap Φ K τ X := by
  simp only [channelMap, outputBlock_smul, Matrix.smul_kronecker]
  exact Matrix.blockDiagonal'_smul c (fun j => outputBlock Φ K j X ⊗ₖ (τ j).matrix)

theorem channelMap_trace (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j))
    (X : Matrix (Σ i, α i × χ i) (Σ i, α i × χ i) ℂ) :
    Matrix.trace (channelMap Φ K τ X) = Matrix.trace X := by
  simp only [channelMap, Matrix.trace_blockDiagonal', Matrix.trace_kronecker,
    State.trace_one, mul_one, outputBlock_trace]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Complex.ofReal_sum, hKsum, Complex.ofReal_one, one_mul]
  exact inputReduction_trace_sum X

theorem channelMap_completely_positive (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j) (τ : ∀ j, State (κ j)) (k : ℕ)
    (X : Matrix (Fin k × (Σ i, α i × χ i)) (Fin k × (Σ i, α i × χ i)) ℂ)
    (hX : X.PosSemidef) : (amplify (channelMap Φ K τ) X).PosSemidef := by
  let B : ∀ j, Matrix (Fin k × (β j × κ j)) (Fin k × (β j × κ j)) ℂ :=
    fun j => ((amplify (outputBlock Φ K j) X) ⊗ₖ (τ j).matrix).submatrix
      (fun a => ((a.1, a.2.1), a.2.2)) (fun a => ((a.1, a.2.1), a.2.2))
  have hB : ∀ j, (B j).PosSemidef := fun j =>
    ((outputBlock_completely_positive Φ K hK j k X hX).kronecker
      (τ j).positive).submatrix _
  have hd := (blockDiagonal'_posSemidef B hB).submatrix
    (fun a : Fin k × (Σ j, β j × κ j) => ⟨a.2.1, (a.1, a.2.2)⟩)
  convert hd using 1
  ext ⟨a, j, b, t⟩ ⟨a', j', b', t'⟩
  by_cases hj : j = j'
  · subst j'
    simp [channelMap, amplify, B, Matrix.kroneckerMap_apply]
  · simp [channelMap, amplify, B, Matrix.blockDiagonal'_apply_ne, hj]

/-- The sector construction is a genuine CPTP map for arbitrary sector
channels and stochastic kernel, with no assumptions on its input matrix. -/
def channel (Φ : ∀ i j, MatrixChannel (α i) (β j))
    (K : μ → ν → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1) (τ : ∀ j, State (κ j)) :
    MatrixChannel (Σ i, α i × χ i) (Σ j, β j × κ j) where
  toFun := channelMap Φ K τ
  map_add := channelMap_add Φ K τ
  map_smul := channelMap_smul Φ K τ
  trace_preserving := channelMap_trace Φ K hKsum τ
  completely_positive := channelMap_completely_positive Φ K hK τ

end Cloning.MatrixLiftedCPTP
