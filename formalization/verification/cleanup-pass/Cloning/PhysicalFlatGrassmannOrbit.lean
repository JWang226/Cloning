import Cloning.PhysicalFlatGrassmannSpectral
import Cloning.PhysicalFlatConverseOrbit

/-! Literal rank-r orthogonal projectors, normalized projector density
states, and surjectivity of the actual unitary-orbit parameterization. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace Cloning.PhysicalFlatGrassmann
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {r k : ℕ}

/-- The Grassmann family consists of actual matrices with the three stated
properties. Its definition contains no unitary-orbit or spectral witness. -/
def Projector (r k : ℕ) := {P : Matrix (Fin (r+k)) (Fin (r+k)) ℂ //
  P.IsHermitian ∧ P*P=P ∧ P.rank=r}

theorem coordinateProjector_nonneg (r k : ℕ) : (coordinateProjector r k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ if i.val < r then 1 else 0
  split_ifs <;> positivity

theorem coordinateProjector_idempotent (r k : ℕ) :
    coordinateProjector r k * coordinateProjector r k = coordinateProjector r k := by
  simp only [coordinateProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem coordinateProjector_rank (r k : ℕ) : (coordinateProjector r k).rank = r := by
  rw [coordinateProjector, Matrix.rank_diagonal]
  let e : {i : Fin (r+k) // (if i.val < r then (1 : ℂ) else 0) ≠ 0} ≃
      {i : Fin (r+k) // i.val < r} :=
    Equiv.subtypeEquivRight (fun i => by split_ifs <;> simp_all)
  rw [Fintype.card_congr e]
  exact Fintype.card_fin_lt_of_le (Nat.le_add_right r k)

theorem coordinateProjector_trace (r k : ℕ) : Matrix.trace (coordinateProjector r k) = (r : ℂ) := by
  rw [coordinateProjector, Matrix.trace_diagonal, Fin.sum_univ_add]
  simp

/-- Every physical unitary yields a literal rank-r orthogonal projector. -/
def orbitProjector (r k : ℕ) (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    Projector r k := by
  let V : Matrix (Fin (r+k)) (Fin (r+k)) ℂ := U
  have hV : Vᴴ*V=1 := Unitary.star_mul_self_of_mem U.property
  refine ⟨V * coordinateProjector r k * Vᴴ,
    ((coordinateProjector_nonneg r k).mul_mul_conjTranspose_same V).isHermitian,?_,?_⟩
  · calc
      _ = V * coordinateProjector r k * (Vᴴ*V) * coordinateProjector r k * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V, coordinateProjector_idempotent]
  · have hstar : IsUnit Vᴴ.det := Matrix.UnitaryGroup.det_isUnit (star U)
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hstar,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit U),
      coordinateProjector_rank]

theorem orbitProjector_surjective (r k : ℕ) : Function.Surjective (orbitProjector r k) := by
  intro P
  obtain ⟨U,hU⟩ := exists_unitary_projector P.val P.property.1 P.property.2.1 P.property.2.2
  exact ⟨U,Subtype.ext hU.symm⟩

theorem projector_nonneg (P : Projector r k) : P.val.PosSemidef := by
  obtain ⟨U,rfl⟩ := orbitProjector_surjective r k P
  exact (coordinateProjector_nonneg r k).mul_mul_conjTranspose_same
    (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)

theorem projector_trace (P : Projector r k) : Matrix.trace P.val = (r : ℂ) := by
  obtain ⟨U,rfl⟩ := orbitProjector_surjective r k P
  change Matrix.trace ((U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * coordinateProjector r k * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ) = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hU : (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem U.property
  rw [hU, Matrix.one_mul, coordinateProjector_trace]

/-- The normalized density is literally P/r. -/
def state (hr : 0 < r) (P : Projector r k) : Cloning.MatrixFidelity.State (Fin (r+k)) where
  matrix := (1/(r : ℝ)) • P.val
  positive := (projector_nonneg P).smul (by positivity)
  trace_one := by
    rw [Matrix.trace_smul, projector_trace, Complex.real_smul]
    push_cast
    simpa only [one_div] using inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hr) : (r : ℂ) ≠ 0)

theorem flatState_matrix (r k : ℕ) (hr : 0 < r) :
    (Cloning.PhysicalFlatConverse.flatState r k hr).matrix = (1/(r : ℝ)) • coordinateProjector r k := by
  ext i j
  simp only [Cloning.PhysicalFlatConverse.flatState, diagonalState, coordinateProjector,
    rankFlatSpectrum, Matrix.diagonal_apply, Matrix.smul_apply]
  split_ifs <;> simp_all

theorem state_orbitProjector (r k : ℕ) (hr : 0 < r)
    (U : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ)) :
    state hr (orbitProjector r k U) = Cloning.PhysicalFlatConverse.orbitState r k hr U := by
  have hm : (state hr (orbitProjector r k U)).matrix =
      (Cloning.PhysicalFlatConverse.orbitState r k hr U).matrix := by
    change (1/(r : ℝ)) • ((U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * coordinateProjector r k * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ) =
      (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * (Cloning.PhysicalFlatConverse.flatState r k hr).matrix * (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ
    rw [flatState_matrix, Matrix.mul_smul, Matrix.smul_mul]
  cases h₁ : state hr (orbitProjector r k U)
  cases h₂ : Cloning.PhysicalFlatConverse.orbitState r k hr U
  simp only [h₁,h₂,Cloning.MatrixFidelity.State.mk.injEq] at hm ⊢
  exact hm

end Cloning.PhysicalFlatGrassmann
