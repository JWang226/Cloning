import Cloning.PCTGlobalPhysical

/-! Rectangular tensor powers intertwine the literal physical symmetric
projectors. These identities apply to every complex matrix, before any
purification state or rank-adapted channel is selected. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

local instance finiteRegister (I : Type*) [Fintype I] [DecidableEq I] :
    FiniteDimensional ℂ (Register I) :=
  (registerBasis I).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def tensorMap (L : ℕ) (J : Matrix B A ℂ) :
    Register (Fin L → A) →L[ℂ] Register (Fin L → B) :=
  matrixRegister (tensorPower L J)

def wordReindex {L : ℕ} (σ : Equiv.Perm (Fin L)) :
    (Fin L → A) ≃ (Fin L → A) where
  toFun w := w ∘ σ
  invFun w := w ∘ σ.symm
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

@[simp] theorem tensorMap_apply (L : ℕ) (J : Matrix B A ℂ)
    (x : Register (Fin L → A)) (v : Fin L → B) :
    tensorMap L J x v = ∑ w, x w * ∏ i, J (v i) (w i) := by
  simp only [tensorMap, matrixRegister_apply, tensorPower, mul_comm]

theorem tensorMap_permute (L : ℕ) (J : Matrix B A ℂ)
    (σ : Equiv.Perm (Fin L)) (x : Register (Fin L → A)) :
    tensorMap L J (permuteRegister σ x) = permuteRegister σ (tensorMap L J x) := by
  ext v
  simp only [tensorMap_apply, permuteRegister_apply]
  calc
    _ = ∑ w : Fin L → A, x w * ∏ i, J (v i) (w (σ.symm i)) := by
      have he := (wordReindex (A:=A) σ.symm).sum_comp
        (fun w => x (w ∘ σ) * ∏ i, J (v i) (w i))
      have hc (w : Fin L → A) : (w ∘ σ.symm) ∘ σ = w := by funext i; simp
      simpa only [wordReindex, Equiv.coe_fn_mk, hc, Function.comp_apply] using he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      congr 1
      have he := Equiv.prod_comp σ (fun i => J (v i) (w (σ.symm i)))
      simpa only [Equiv.symm_apply_apply, Function.comp_apply] using he.symm

@[simp] theorem tensorMap_adjoint (L : ℕ) (J : Matrix B A ℂ) :
    (tensorMap L J).adjoint = tensorMap L Jᴴ := by
  rw [tensorMap, tensorMap, tensorPower_star, matrixRegister_conjTranspose]

theorem tensorMap_symmetric (L : ℕ) (J : Matrix B A ℂ)
    (x : Register (Fin L → A)) (hx : x ∈ physicalSymmetric L) :
    tensorMap L J x ∈ physicalSymmetric L := by
  intro v σ
  have hp : permuteRegister σ x = x := by ext w; exact hx w σ
  have he := tensorMap_permute L J σ x
  rw [hp] at he
  exact (congrArg (fun y : Register (Fin L → B) => y v) he).symm

/-- Naturality of the symmetric projector under an arbitrary rectangular
one-particle matrix; no surjectivity or full-frame premise is needed. -/
theorem tensorMap_physicalProjector (L : ℕ) (J : Matrix B A ℂ)
    (x : Register (Fin L → A)) :
    physicalProjector L (tensorMap L J x) = tensorMap L J (physicalProjector L x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact tensorMap_symmetric L J _ ((physicalSymmetric L).starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, tensorMap_adjoint]
    exact (Submodule.mem_orthogonal' _ _).mp
      ((physicalSymmetric (C:=A) L).sub_starProjection_mem_orthogonal x) _
      (tensorMap_symmetric L Jᴴ w hw)

/-- Tensor powers of an actual one-particle isometry are actual isometries. -/
theorem tensorMap_adjoint_comp_self (L : ℕ) (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1) :
    (tensorMap L J).adjoint.comp (tensorMap L J) = ContinuousLinearMap.id ℂ _ := by
  rw [tensorMap_adjoint, tensorMap, tensorMap, ← matrixRegister_mul,
    ← tensorPower_mul, hJ, tensorPower_one, matrixRegister_one]

end Cloning.PCTRankAdapted
