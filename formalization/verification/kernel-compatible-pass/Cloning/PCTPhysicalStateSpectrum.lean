import Cloning.PCTPhysicalFidelityUnitary
import Mathlib.Analysis.Matrix.PosDef

/-! Construct the actual ordered simple spectrum and its unitary
diagonalization from a positive definite density matrix with distinct
eigenvalues. No diagonalizing-unitary premise is assumed. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Topology
open MeasureTheory Filter
namespace Cloning.PCTPhysicalState
open Cloning.PCTUnitaryTransport Cloning.PCTPhysicalFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {D : ℕ}

def orderedIndex (D : ℕ) : Fin D ≃ Fin D :=
  (finCongr (Fintype.card_fin D).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin D))))

def orderedEigenvalues (ρ : Cloning.MatrixFidelity.State (Fin D)) : Fin D → ℝ :=
  fun i => ρ.positive.isHermitian.eigenvalues (orderedIndex D i)

theorem orderedEigenvalues_eq (ρ : Cloning.MatrixFidelity.State (Fin D)) (i : Fin D) :
    orderedEigenvalues ρ i = ρ.positive.isHermitian.eigenvalues₀
      ((finCongr (Fintype.card_fin D).symm) i) := by
  simp only [orderedEigenvalues, orderedIndex, Equiv.trans_apply, Matrix.IsHermitian.eigenvalues,
    Equiv.symm_apply_apply]

theorem orderedEigenvalues_antitone (ρ : Cloning.MatrixFidelity.State (Fin D)) :
    Antitone (orderedEigenvalues ρ) := by
  intro i j hij
  simp only [orderedEigenvalues_eq]
  exact ρ.positive.isHermitian.eigenvalues₀_antitone hij

theorem orderedEigenvalues_sum (ρ : Cloning.MatrixFidelity.State (Fin D)) :
    ∑ i, orderedEigenvalues ρ i = 1 := by
  have h := congrArg Complex.re ρ.positive.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.trace_one] at h
  simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h
  change (∑ i, ρ.positive.isHermitian.eigenvalues (orderedIndex D i)) = 1
  rw [(orderedIndex D).sum_comp]
  exact h.symm

def densitySpectrum (ρ : Cloning.MatrixFidelity.State (Fin D)) (hpos : ρ.matrix.PosDef)
    (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues) : SimpleSpectrum D where
  eigenvalue := orderedEigenvalues ρ
  positive := fun i => hpos.eigenvalues_pos _
  normalized := orderedEigenvalues_sum ρ
  strictAnti := (orderedEigenvalues_antitone ρ).strictAnti_of_injective
    (hsimple.comp (orderedIndex D).injective)

def orderedUnitary (ρ : Cloning.MatrixFidelity.State (Fin D)) :
    unitary (Matrix (Fin D) (Fin D) ℂ) :=
  ⟨fun i j => (ρ.positive.isHermitian.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)
      i (orderedIndex D j), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext i j
    have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M (orderedIndex D i) (orderedIndex D j))
      (Unitary.star_mul_self_of_mem ρ.positive.isHermitian.eigenvectorUnitary.property)
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, (orderedIndex D).injective.eq_iff] using h⟩

theorem orderedUnitary_intertwines (ρ : Cloning.MatrixFidelity.State (Fin D)) :
    ρ.matrix * (orderedUnitary ρ : Matrix (Fin D) (Fin D) ℂ) =
      (orderedUnitary ρ : Matrix (Fin D) (Fin D) ℂ) *
        Matrix.diagonal (fun i => (orderedEigenvalues ρ i : ℂ)) := by
  ext i j
  rw [Matrix.mul_diagonal]
  have h := congrFun (ρ.positive.isHermitian.mulVec_eigenvectorBasis (orderedIndex D j)) i
  simpa only [orderedUnitary, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.IsHermitian.eigenvectorUnitary_apply, orderedEigenvalues,
    Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul, mul_comm] using h

theorem orderedUnitary_diagonalizes (ρ : Cloning.MatrixFidelity.State (Fin D)) :
    ρ.matrix = (orderedUnitary ρ : Matrix (Fin D) (Fin D) ℂ) *
      Matrix.diagonal (fun i => (orderedEigenvalues ρ i : ℂ)) *
        (orderedUnitary ρ : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  rw [← orderedUnitary_intertwines, Matrix.mul_assoc]
  have hU : (orderedUnitary ρ : Matrix (Fin D) (Fin D) ℂ) *
      (orderedUnitary ρ : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (orderedUnitary ρ).property
  rw [hU, Matrix.mul_one]

/-- Arbitrary positive definite states with distinct actual eigenvalues are
covered by the physical theorem; their spectrum and unitary are constructed. -/
theorem physical_pct_fidelity_of_simple_density {k d s : ℕ}
    (ρ : Cloning.MatrixFidelity.State (Fin (k+1))) (hpos : ρ.matrix.PosDef)
    (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues)
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0 = Cloning.PCTJointGaussianWhitening.sqrtSpectrum (densitySpectrum ρ hpos hsimple).eigenvalue)
    (e : Fin d ≃ PairIndex (k+1))
    (lan : CompactWindowLAN (densitySpectrum ρ hpos hsimple) b e)
    (hs : 1 ≤ s) (hcard : Fintype.card (Fin (k+1) × Fin (k+1)) = s+1)
    (r : ℕ → ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hr : Tendsto (fun n => ((n+r n : ℕ) : ℝ) / n) atTop (𝓝 γ)) :
    Tendsto (fun n => (outputState hcard ρ n (r n)).rootFidelity
      (tensorState ρ (n+r n))) atTop (𝓝 (pctValue γ (densitySpectrum ρ hpos hsimple))) :=
  physical_pct_fidelity_of_diagonalization (densitySpectrum ρ hpos hsimple) b hb e lan
    ρ (orderedUnitary ρ) (orderedUnitary_diagonalizes ρ) hs hcard r γ hγ hr

end Cloning.PCTPhysicalState
