import Cloning.PCTRankPurificationFlatOrbit
import Cloning.PhysicalFlatGrassmannIsometry

/-! The one fixed rank purifier has its literal embedded Haar action on
any isometric embedding of the supported maximally mixed density. -/
noncomputable section
open scoped Matrix Kronecker ComplexOrder
namespace Cloning.PCTRankPurification
open Cloning.PCTPurificationChannel Cloning.PCTRankAdapted Cloning.PhysicalFlatGrassmann Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance flatStateAmbientNeZero (d k : ℕ) : NeZero (d+1+k) := ⟨by omega⟩

theorem flatInternalState_matrix_complex (d : ℕ) :
    (flatInternalState d).matrix = (1/((d+1 : ℕ):ℂ)) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) := by
  ext a b
  simp [flatInternalState, Cloning.PCTPhysicalState.diagonalState, Cloning.YoungGeneral.flatSpectrum,
    Matrix.diagonal_apply, Matrix.one_apply, Matrix.smul_apply]

/-- The construction always uses the fixed coordinate inclusion. The input
isometry J is arbitrary and does not choose or modify the channel. -/
theorem rankPurificationChannel_flatState (d k n : ℕ)
    (b0 : (Fin n → Fin (d+1+k)) × (Fin n → Fin (d+1)))
    (J : Matrix (Fin (d+1+k)) (Fin (d+1)) ℂ) (hJ : Jᴴ*J=1) :
    (rankPurificationChannel n (coordinateInclusionMatrix (d+1) k) b0).toFun
      (tensorPower n (embeddedState J hJ (flatInternalState d)).matrix) =
      (tensorPower n J ⊗ₖ (1 : Matrix (Fin n → Fin (d+1)) (Fin n → Fin (d+1)) ℂ)) *
        (haarPurificationChannel (A:=Fin (d+1)) n).toFun (tensorPower n (flatInternalState d).matrix) *
      (tensorPower n J ⊗ₖ (1 : Matrix (Fin n → Fin (d+1)) (Fin n → Fin (d+1)) ℂ))ᴴ := by
  obtain ⟨U,hU⟩ := exists_unitary_isometry (d+1) k J hJ
  change J=U.val*coordinateInclusionMatrix (d+1) k at hU
  change (rankPurificationChannel n (coordinateInclusionMatrix (d+1) k) b0).toFun
      (tensorPower n (J*(flatInternalState d).matrix*Jᴴ)) = _
  rw [flatInternalState_matrix_complex,hU]
  exact rankPurificationChannel_flat_orbit n k b0 U (1/((d+1 : ℕ):ℂ))

end Cloning.PCTRankPurification
