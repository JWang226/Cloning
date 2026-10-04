import Cloning.PCTRankAdaptedCompression

/-! Exact trace-class compression of normalized physical Werner outputs,
with the symmetric-dimension ratio derived from the literal sandwich. -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix ComplexOrder
namespace Cloning.PCTRankAdapted
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.FiniteKrausLift
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem matrixRegister_inner (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (x y : Register A) : ⟪matrixRegister J x, matrixRegister J y⟫_ℂ = ⟪x,y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have h : (matrixRegister J).adjoint (matrixRegister J y) = y := by
    change ((matrixRegister J).adjoint.comp (matrixRegister J)) y = y
    rw [← matrixRegister_conjTranspose, ← matrixRegister_mul, hJ, matrixRegister_one]
    rfl
  rw [h]

def matrixIsometry (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1) : Register A →ₗᵢ[ℂ] Register B :=
  (matrixRegister J).toLinearMap.isometryOfInner (matrixRegister_inner J hJ)

@[simp] theorem matrixIsometry_apply (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (x : Register A) : matrixIsometry J hJ x = matrixRegister J x := rfl

theorem matrixRegister_norm (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1) (x : Register A) :
    ‖matrixRegister J x‖ = ‖x‖ := (matrixIsometry J hJ).norm_map x

def wernerScale (n m s : ℕ) : ℝ := (Nat.choose (n+s) s : ℝ) / Nat.choose (m+s) s

theorem wernerScale_pos (n m s : ℕ) : 0 < wernerScale n m s := by
  apply div_pos
  · exact_mod_cast Nat.choose_pos (by omega : s ≤ n+s)
  · exact_mod_cast Nat.choose_pos (by omega : s ≤ m+s)

/-- Exact support mass as the quotient of ambient and internal symmetric
cloning normalizations. -/
def supportFactor (n m small large : ℕ) : ℝ :=
  wernerScale n m large / wernerScale n m small

theorem supportFactor_pos (n m small large : ℕ) : 0 < supportFactor n m small large :=
  div_pos (wernerScale_pos n m large) (wernerScale_pos n m small)

/-- The uncompressed output is the actual normalized physical pure-state
Werner operator, and the compressed output is the smaller physical Werner
operator times the exact dimension ratio. -/
theorem pureWernerOutput_compression {L small large : ℕ}
    (hA : Fintype.card A = small+1) (hB : Fintype.card B = large+1)
    (J : Matrix B A ℂ) (hJ : Jᴴ * J = 1)
    (ψ : Register A) (hψ : ‖ψ‖ = 1) (S : Finset (Fin L)) :
    conjugationLinearMap (tensorMap L J).adjoint
      (pureWernerOutput hB (matrixRegister J ψ) ((matrixRegister_norm J hJ ψ).trans hψ) S) =
      (supportFactor S.card L small large : ℂ) • pureWernerOutput hA ψ hψ S := by
  apply Subtype.ext
  change operatorConjugation (tensorMap L J).adjoint
    (pureWernerOperator large (matrixRegister J ψ) S) =
    (supportFactor S.card L small large : ℂ) • pureWernerOperator small ψ S
  simp only [pureWernerOperator, map_smul]
  have he : operatorConjugation (tensorMap L J).adjoint
      (physicalProjector L * pureSlotsOperator (matrixRegister J ψ) S * physicalProjector L) =
      physicalProjector L * pureSlotsOperator ψ S * physicalProjector L := by
    have hh := wernerSandwich_compression J hJ ψ S
    simpa only [operatorConjugation, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc] using hh
  rw [he, smul_smul]
  congr 1
  change (wernerScale S.card L large : ℂ) =
    (supportFactor S.card L small large : ℂ) * (wernerScale S.card L small : ℂ)
  rw [← Complex.ofReal_mul, supportFactor,
    div_mul_cancel₀ _ (wernerScale_pos S.card L small).ne']

end Cloning.PCTRankAdapted
