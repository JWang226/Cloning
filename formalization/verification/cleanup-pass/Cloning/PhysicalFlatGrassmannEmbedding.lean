import Cloning.PhysicalFlatGrassmannOrbit
import Cloning.PCTRankAdaptedFlat

/-! Every literal Grassmann density is an isometric embedding of the
canonical supported maximally mixed state. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Cloning.PhysicalFlatGrassmann
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- Coordinate inclusion of the supported physical one-particle space. -/
def coordinateInclusion (r k : ℕ) : Matrix (Fin (r+k)) (Fin r) ℂ :=
  fun i a => if i = Fin.castAdd k a then 1 else 0

theorem coordinateInclusion_isometry (r k : ℕ) :
    (coordinateInclusion r k)ᴴ * coordinateInclusion r k = 1 := by
  ext a b
  simp [coordinateInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fin.castAdd_inj, eq_comm]

theorem coordinateInclusion_range (r k : ℕ) :
    coordinateInclusion r k * (coordinateInclusion r k)ᴴ = coordinateProjector r k := by
  have hcross (a : Fin r) (b : Fin k) : Fin.castAdd k a ≠ Fin.natAdd r b := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [coordinateInclusion, coordinateProjector, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, hcross, eq_comm]

/-- Every rank-r orthogonal projector has an actual r-column isometric
factorization. This is stronger than a supplied support witness. -/
theorem exists_isometric_factor (r k : ℕ) (P : Projector r k) :
    ∃ J : Matrix (Fin (r+k)) (Fin r) ℂ, Jᴴ*J=1 ∧ P.val=J*Jᴴ := by
  obtain ⟨U,hU⟩ := orbitProjector_surjective r k P
  let V : Matrix (Fin (r+k)) (Fin (r+k)) ℂ := U
  have hV : Vᴴ*V=1 := Unitary.star_mul_self_of_mem U.property
  refine ⟨V*coordinateInclusion r k,?_,?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc
      _ = (coordinateInclusion r k)ᴴ * (Vᴴ*V) * coordinateInclusion r k := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV, Matrix.mul_one, coordinateInclusion_isometry]
  · have he : P.val=V*coordinateProjector r k*Vᴴ := congrArg Subtype.val hU.symm
    rw [he, Matrix.conjTranspose_mul, ← coordinateInclusion_range]
    simp only [Matrix.mul_assoc]

open Cloning.PCTRankAdapted Cloning.PCTPhysicalState
local instance (d k : ℕ) : Nonempty (Fin (d+1+k)) := ⟨⟨0,by omega⟩⟩

theorem flatInternalState_matrix (d : ℕ) :
    (flatInternalState d).matrix = (1/(d+1 : ℝ)) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) := by
  ext a b
  simp [flatInternalState, diagonalState, Cloning.YoungGeneral.flatSpectrum,
    Matrix.diagonal_apply, Matrix.one_apply]

theorem exists_embedded_flatState (d k : ℕ) (P : Projector (d+1) k) :
    ∃ J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ, ∃ hJ : Jᴴ*J=1,
      state (by omega : 0<d+1) P = embeddedState J hJ (flatInternalState d) := by
  obtain ⟨J,hJ,hP⟩ := exists_isometric_factor (d+1) k P
  refine ⟨J,hJ,?_⟩
  have hm : (state (by omega : 0<d+1) P).matrix =
      (embeddedState J hJ (flatInternalState d)).matrix := by
    change (1/((d+1 : ℕ):ℝ)) • P.val = J*(flatInternalState d).matrix*Jᴴ
    rw [flatInternalState_matrix, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hP]
    simp only [Nat.cast_add, Nat.cast_one]
  cases h₁ : state (by omega : 0<d+1) P
  cases h₂ : embeddedState J hJ (flatInternalState d)
  simp only [h₁,h₂,Cloning.MatrixFidelity.State.mk.injEq] at hm ⊢
  exact hm

end Cloning.PhysicalFlatGrassmann
