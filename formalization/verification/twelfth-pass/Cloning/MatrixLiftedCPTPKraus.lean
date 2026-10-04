import Cloning.MatrixLiftedCPTPAction
import Cloning.FiniteKrausLift

/-!
# Finite Kraus realization without a representation premise

Every actual finite matrix channel has a normalized Kraus family, obtained
from the positive square root of its Choi matrix. Consequently the lifted
sector channel also acts on the actual Hilbert-space trace-class registers.
-/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker
open Matrix Cloning.Channels Cloning.MatrixFidelity

namespace Cloning.MatrixLiftedCPTP

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem amplify_posSemidef {ι : Type*} [Fintype ι]
    (Φ : MatrixChannel α β) (X : Matrix (ι × α) (ι × α) ℂ) (hX : X.PosSemidef) :
    (amplify Φ.toFun X).PosSemidef := by
  let e := Fintype.equivFin ι
  have h := (Φ.completely_positive (Fintype.card ι) _
    (hX.submatrix (fun a : Fin (Fintype.card ι) × α => (e.symm a.1, a.2)))).submatrix
    (fun a : ι × β => (e a.1, a.2))
  convert h using 1
  ext a b
  simp [amplify, Matrix.submatrix]

/-- The Choi matrix, with input and output indices in that order. -/
def choi (Φ : MatrixChannel α β) : Matrix (α × β) (α × β) ℂ :=
  fun a b => Φ.toFun (Matrix.single a.1 b.1 1) a.2 b.2

theorem choi_posSemidef (Φ : MatrixChannel α β) : (choi Φ).PosSemidef := by
  let v : α × α → ℂ := fun a => if a.1 = a.2 then 1 else 0
  have h := amplify_posSemidef Φ _ (Matrix.posSemidef_vecMulVec_self_star v)
  convert h using 1
  ext ⟨a, b⟩ ⟨c, d⟩
  change Φ.toFun (Matrix.single a c 1) b d =
    Φ.toFun (fun i j => v (a, i) * star (v (c, j))) b d
  congr 1
  ext i j
  by_cases hi : a = i <;> by_cases hj : c = j <;> simp [v, hi, hj]

/-- A canonical finite rectangular Kraus family from the Choi square root. -/
def choiKraus (Φ : MatrixChannel α β) (l : α × β) : Matrix β α ℂ :=
  fun b a => CFC.sqrt (choi Φ) (a, b) l

theorem choiKraus_coefficient (Φ : MatrixChannel α β) (a c : α) (b d : β) :
    (∑ l, choiKraus Φ l b a * star (choiKraus Φ l d c)) =
      Φ.toFun (Matrix.single a c 1) b d := by
  have h : CFC.sqrt (choi Φ) * (CFC.sqrt (choi Φ)).conjTranspose = choi Φ := by
    rw [sqrt_conjTranspose, sqrt_mul_self (choi_posSemidef Φ)]
  exact congrArg (fun M => M (a, b) (c, d)) h

theorem channel_matrix_expansion (Φ : MatrixChannel α β) (X : Matrix α α ℂ) :
    Φ.toFun X = ∑ a, ∑ c, X a c • Φ.toFun (Matrix.single a c 1) := by
  have hX : X = ∑ a, ∑ c, X a c • (Matrix.single a c 1 : Matrix α α ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
  change (channelLinearMap Φ) X = _
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, channelLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- The canonical Kraus formula equals the given channel on every complex input. -/
theorem choiKraus_apply (Φ : MatrixChannel α β) (X : Matrix α α ℂ) :
    krausMap (choiKraus Φ) X = Φ.toFun X := by
  rw [channel_matrix_expansion Φ X]
  ext b d
  simp only [krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← choiKraus_coefficient Φ a c b d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Trace preservation of the original channel proves Kraus normalization;
the normalization is not a hypothesis on the construction. -/
theorem choiKraus_complete (Φ : MatrixChannel α β) :
    (∑ l, (choiKraus Φ l).conjTranspose * choiKraus Φ l) = 1 := by
  ext a c
  calc
    (∑ l, (choiKraus Φ l).conjTranspose * choiKraus Φ l) a c =
        ∑ b, Φ.toFun (Matrix.single c a 1) b b := by
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [← choiKraus_coefficient Φ c a b b]
      apply Finset.sum_congr rfl
      intro l _
      exact mul_comm _ _
    _ = Matrix.trace (Φ.toFun (Matrix.single c a 1)) := rfl
    _ = Matrix.trace (Matrix.single c a 1) := Φ.trace_preserving _
    _ = (1 : Matrix α α ℂ) a c := by
      simp [Matrix.trace, Matrix.diag, Matrix.single_apply, Matrix.one_apply, ite_and]

open Cloning.InfiniteTraceClass Cloning.PCT Cloning.PCTPurificationChannel

/-- Every finite matrix CPTP map becomes a CPTP map of the actual Hilbert
register trace-class spaces, without supplying any extra representation data. -/
def registerChannel (Φ : MatrixChannel α β) : QuantumChannel (Register α) (Register β) :=
  FiniteKrausLift.channel (choiKraus Φ) (choiKraus_complete Φ)

/-- Exact agreement on every matrix, including nonpositive off-diagonal inputs. -/
theorem registerChannel_matrix (Φ : MatrixChannel α β) (X : Matrix α α ℂ) :
    (registerChannel Φ).toLinearMap (registerLiftCLM X) = registerLiftCLM (Φ.toFun X) := by
  rw [registerChannel, FiniteKrausLift.channel_registerLiftCLM, choiKraus_apply]

/-- Exact agreement also stated on all physical trace-class inputs. -/
theorem registerChannel_apply (Φ : MatrixChannel α β) (T : TraceClass (Register α)) :
    (registerChannel Φ).toLinearMap T = registerLiftCLM
      (Φ.toFun (InfiniteFiniteCorner.matrixOf (registerBasis α) T.1)) := by
  have hT : registerLiftCLM (InfiniteFiniteCorner.matrixOf (registerBasis α) T.1) = T := by
    apply Subtype.ext
    apply register_operator_ext
    intro a b
    rw [registerLiftCLM_coefficient]
    simp [InfiniteFiniteCorner.matrixOf, registerBasis_apply, register_inner_single]
  simpa only [hT] using registerChannel_matrix Φ
    (InfiniteFiniteCorner.matrixOf (registerBasis α) T.1)

end Cloning.MatrixLiftedCPTP
