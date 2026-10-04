import Cloning.PCTPhysicalStateSpectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic

/-! Every actual Hermitian idempotent of rank r is a unitary conjugate of
the coordinate rank-r projector. The rank and projector assumptions are
literal matrix properties, with no supplied diagonalizer. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace Cloning.PhysicalFlatGrassmann
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {r k : ℕ}

def coordinateProjector (r k : ℕ) : Matrix (Fin (r+k)) (Fin (r+k)) ℂ :=
  Matrix.diagonal (fun i => if i.val < r then 1 else 0)

theorem eigenvalue_zero_or_one {P : Matrix (Fin (r+k)) (Fin (r+k)) ℂ}
    (hP : P.IsHermitian) (hPP : P*P=P) (i : Fin (r+k)) :
    hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
  have h := congrArg (Unitary.conjStarAlgAut ℂ _ (star hP.eigenvectorUnitary)) hPP
  rw [map_mul, hP.conjStarAlgAut_star_eigenvectorUnitary] at h
  have hi := congrArg (fun M : Matrix (Fin (r+k)) (Fin (r+k)) ℂ => (M i i).re) h
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hi
  have hz : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (by linarith)

/-- A permutation orders the actual zero/one eigenvalues into r ones and k
zeros, with cardinalities derived from the literal matrix rank. -/
theorem exists_projector_eigenvalue_order
    {P : Matrix (Fin (r+k)) (Fin (r+k)) ℂ}
    (hP : P.IsHermitian) (hPP : P*P=P) (hrank : P.rank = r) :
    ∃ e : Fin (r+k) ≃ Fin (r+k), ∀ i,
      hP.eigenvalues (e i) = if i.val < r then 1 else 0 := by
  let p : Fin (r+k) → Prop := fun i => hP.eigenvalues i ≠ 0
  have hc : Fintype.card {i // p i} = r := hP.rank_eq_card_non_zero_eigs.symm.trans hrank
  have hz : Fintype.card {i // ¬p i} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hc]
    omega
  let ep : Fin r ≃ {i // p i} := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hc])
  let ez : Fin k ≃ {i // ¬p i} := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hz])
  let e : Fin (r+k) ≃ Fin (r+k) := finSumFinEquiv.symm.trans
    ((ep.sumCongr ez).trans (Equiv.sumCompl p))
  refine ⟨e,?_⟩
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hp : hP.eigenvalues (ep j).val ≠ 0 := (ep j).property
    have hv := (eigenvalue_zero_or_one hP hPP (ep j).val).resolve_left hp
    simpa [e, Fin.isLt] using hv
  · have hp : hP.eigenvalues (ez j).val = 0 := not_not.mp (ez j).property
    simpa [e] using hp

def permutedEigenvectorUnitary {P : Matrix (Fin (r+k)) (Fin (r+k)) ℂ}
    (hP : P.IsHermitian) (e : Fin (r+k) ≃ Fin (r+k)) :
    unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ) :=
  ⟨fun i j => (hP.eigenvectorUnitary : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) i (e j), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext i j
    have h := congrArg (fun M : Matrix (Fin (r+k)) (Fin (r+k)) ℂ => M (e i) (e j))
      (Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.property)
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, e.injective.eq_iff] using h⟩

theorem exists_unitary_projector
    (P : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (hrank : P.rank = r) :
    ∃ U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ),
      P = (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * coordinateProjector r k * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ := by
  obtain ⟨e,he⟩ := exists_projector_eigenvalue_order hP hPP hrank
  let U := permutedEigenvectorUnitary hP e
  have hint : P * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) = (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * coordinateProjector r k := by
    ext i j
    rw [coordinateProjector, Matrix.mul_diagonal]
    have h := congrFun (hP.mulVec_eigenvectorBasis (e j)) i
    rw [he j] at h
    split_ifs at h ⊢ <;>
      simpa only [U, permutedEigenvectorUnitary, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Matrix.IsHermitian.eigenvectorUnitary_apply, Pi.smul_apply,
        RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_eq_mul,
        RCLike.ofReal_one, RCLike.ofReal_zero, one_mul, mul_one, zero_mul, mul_zero] using h
  refine ⟨U,?_⟩
  have hU : (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem U.property
  rw [← hint, Matrix.mul_assoc, hU, Matrix.mul_one]

end Cloning.PhysicalFlatGrassmann
