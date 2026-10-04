import Cloning.MatrixFidelityEmbedding
import Cloning.MatrixFidelityScaling
import Cloning.CartanChannel

/-! Exact fidelity under rectangular support compression, and its application
to the dimension-ratio Cartan formula. These matrix lemmas support the physical
rank-restriction theorem for arbitrary spectra. -/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix Kronecker
namespace Cloning.MatrixFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Only the target support contributes to root fidelity; the first argument
may have arbitrary positive mass and coherences outside that support. -/
theorem fidelity_rectangular_compression (J : Matrix m n ℂ) (hJ : Jᴴ*J=1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity A (J*B*Jᴴ)=fidelity (Jᴴ*A*J) B := by
  unfold fidelity
  rw [sqrt_isometric_embedding J hJ hB]
  have hs : (J*CFC.sqrt B*Jᴴ)*A*(J*CFC.sqrt B*Jᴴ)=
      J*(CFC.sqrt B*(Jᴴ*A*J)*CFC.sqrt B)*Jᴴ := by simp only [Matrix.mul_assoc]
  rw [hs,sqrt_isometric_embedding J hJ
    (sandwich_posSemidef (hA.conjTranspose_mul_mul_same J) B)]
  rw [Matrix.trace_mul_comm,←Matrix.mul_assoc,hJ,Matrix.one_mul]

/-- Exact support compression followed by a positive scale gives the square
root of that scale, including singular and non-flat target states. -/
theorem fidelity_of_rectangular_compression (J : Matrix m n ℂ) (hJ : Jᴴ*J=1)
    {A : Matrix m m ℂ} {X B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hX : X.PosSemidef) (hB : B.PosSemidef) (s : ℝ) (hs : 0≤s)
    (hcomp : Jᴴ*A*J=s • X) :
    fidelity A (J*B*Jᴴ)=Real.sqrt s*fidelity X B := by
  rw [fidelity_rectangular_compression J hJ hA hB,hcomp,fidelity_smul_left s X B hs hX]

end Cloning.MatrixFidelity

namespace Cloning.Compression
open Cloning.MatrixFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A B C a b c : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

theorem sectorMap_posSemidef (V : Matrix (A×B) C ℂ) (din dout : ℝ)
    (hr : 0≤din/dout) {X : Matrix A A ℂ} (hX : X.PosSemidef) :
    (sectorMap din dout V X).PosSemidef := by
  rw [Cloning.CartanChannel.sectorMap_eq_kraus V X din dout hr]
  exact Cloning.Channels.krausMap_positive _ hX

/-- Algebraic root-fidelity rank factorization, for arbitrary positive input
and target matrices, using the actual rectangular restriction square. -/
theorem sectorMap_fidelity_factorization
    (Ja : Matrix A a ℂ) (Jb : Matrix B b ℂ) (Jc : Matrix C c ℂ)
    (Vd : Matrix (A×B) C ℂ) (Vr : Matrix (a×b) c ℂ)
    (X : Matrix a a ℂ) (Y : Matrix c c ℂ) (ad bd ar br : ℝ)
    (ha : Jaᴴ*Ja=1) (hb : Jbᴴ*Jb=1) (hc : Jcᴴ*Jc=1)
    (hrestriction : Vd*Jc=(Ja⊗ₖJb)*Vr)
    (had : 0<ad) (hbd : 0<bd) (har : 0<ar) (hbr : 0<br)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    fidelity (sectorMap ad bd Vd (Ja*X*Jaᴴ)) (Jc*Y*Jcᴴ)=
      Real.sqrt ((ad/ar)/(bd/br))*fidelity (sectorMap ar br Vr X) Y := by
  apply fidelity_of_rectangular_compression Jc hc
    (sectorMap_posSemidef Vd ad bd (by positivity) (hX.mul_mul_conjTranspose_same Ja))
    (sectorMap_posSemidef Vr ar br (by positivity) hX) hY _ (by positivity)
  exact sectorMap_compression Ja Jb Jc Vd Vr X ad bd ar br ha hb hrestriction
    hbd.ne' har.ne' hbr.ne'

end Cloning.Compression
