import Cloning.PCTPurificationChannelHaar
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Haar channel acts as random purification on tensor-power inputs

The commutation argument is finite dimensional and uses no Schur--Weyl
decomposition: polynomial uniqueness on the unit circle extends commutation
with diagonal unitaries to all diagonal matrices, then the Hermitian spectral
theorem handles square roots of arbitrary positive inputs.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace Cloning.PCTPurificationChannel

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem infinite_complex_unit_circle : Set.Infinite {z : ℂ | ‖z‖ = 1} := by
  let f : ℝ → ℂ := fun t => ⟨t, Real.sqrt (1 - t ^ 2)⟩
  have hi : Set.InjOn f (Set.Ioo (-1 : ℝ) 1) := by
    intro x _ y _ h
    exact congrArg Complex.re h
  apply ((Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).image hi).mono
  rintro z ⟨t, ht, rfl⟩
  change ‖f t‖ = 1
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hn : ‖f t‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    change t * t + Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1
    rw [Real.mul_self_sqrt ht2]
    ring
  nlinarith [norm_nonneg (f t)]

theorem tensorPower_diagonal (n : ℕ) (z : A → ℂ) :
    tensorPower n (Matrix.diagonal z) = Matrix.diagonal (fun a => ∏ i, z (a i)) := by
  ext a c
  by_cases h : a = c
  · subst c
    simp [tensorPower]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.diagonal_apply_ne _ hi

theorem leftTensor_diagonal (n : ℕ) (z : A → ℂ) :
    leftTensor n (Matrix.diagonal z) =
      Matrix.diagonal (fun ab : (Fin n → A) × (Fin n → A) => ∏ i, z (ab.1 i)) := by
  rw [leftTensor, tensorPower_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_kronecker_diagonal]
  simp

def diagonalUnitary (z : A → ℂ) (hz : ∀ a, ‖z a‖ = 1) : unitary (Matrix A A ℂ) :=
  ⟨Matrix.diagonal z, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (Matrix.diagonal z)ᴴ * Matrix.diagonal z = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext a c
    by_cases h : a = c
    · subst c
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq]
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, one_pow,
        Complex.ofReal_one]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply, h]⟩

/-- Polynomial extension of the diagonal unitary commutation identities. -/
theorem commute_diagonal_of_commute_unitary (n : ℕ)
    (R : Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ)
    (hR : ∀ V : unitary (Matrix A A ℂ), Commute R (leftTensor n (V : Matrix A A ℂ)))
    (z : A → ℂ) : Commute R (leftTensor n (Matrix.diagonal z)) := by
  rw [leftTensor_diagonal]
  show R * Matrix.diagonal _ = Matrix.diagonal _ * R
  ext ab cd
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  let p : MvPolynomial A ℂ := MvPolynomial.C (R ab cd) *
    ∏ i : Fin n, MvPolynomial.X (cd.1 i)
  let q : MvPolynomial A ℂ := (∏ i : Fin n, MvPolynomial.X (ab.1 i)) *
    MvPolynomial.C (R ab cd)
  have hpq : p = q := by
    apply MvPolynomial.funext_set (fun _ => {w : ℂ | ‖w‖ = 1})
      (fun _ => infinite_complex_unit_circle)
    intro w hw
    have hw' : ∀ a, ‖w a‖ = 1 := fun a => hw a (Set.mem_univ a)
    have hc := (hR (diagonalUnitary w hw')).eq
    change R * leftTensor n (Matrix.diagonal w) = leftTensor n (Matrix.diagonal w) * R at hc
    rw [leftTensor_diagonal] at hc
    have he := congrArg (fun M => M ab cd) hc
    simpa [p, q, MvPolynomial.eval_prod, Matrix.mul_diagonal, Matrix.diagonal_mul] using he
  have he := congrArg (MvPolynomial.eval z) hpq
  simpa [p, q, MvPolynomial.eval_prod] using he

theorem haarMoment_commute_diagonal (n : ℕ) (z : A → ℂ) :
    Commute (haarMoment (A := A) n) (leftTensor n (Matrix.diagonal z)) :=
  commute_diagonal_of_commute_unitary n _ (haarMoment_commute_unitary n) z

/-- Unitary commutation extends to every Hermitian tensor-power input. -/
theorem commute_hermitian_of_commute_unitary (n : ℕ)
    (R : Matrix ((Fin n → A) × (Fin n → A)) ((Fin n → A) × (Fin n → A)) ℂ)
    (hR : ∀ V : unitary (Matrix A A ℂ), Commute R (leftTensor n (V : Matrix A A ℂ)))
    (X : Matrix A A ℂ) (hX : X.IsHermitian) : Commute R (leftTensor n X) := by
  have hx : X = (hX.eigenvectorUnitary : Matrix A A ℂ) *
      Matrix.diagonal (fun a => (hX.eigenvalues a : ℂ)) *
      (hX.eigenvectorUnitary : Matrix A A ℂ)ᴴ := hX.spectral_theorem
  rw [hx, leftTensor_mul, leftTensor_mul]
  exact ((hR hX.eigenvectorUnitary).mul_right
    (commute_diagonal_of_commute_unitary n R hR _)).mul_right (hR (star hX.eigenvectorUnitary))

theorem haarMoment_commute_hermitian (n : ℕ) (X : Matrix A A ℂ)
    (hX : X.IsHermitian) : Commute (haarMoment (A := A) n) (leftTensor n X) :=
  commute_hermitian_of_commute_unitary n _ (haarMoment_commute_unitary n) X hX

/-- The pointwise purification coefficient matrix. Vectorizing this matrix
produces a purification of `ρ`, rotated only on its environment. -/
def purificationCoefficients (ρ : Matrix A A ℂ) (U : unitary (Matrix A A ℂ)) :
    Matrix A A ℂ := CFC.sqrt ρ * (U : Matrix A A ℂ)

theorem purificationCoefficients_reduces (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef)
    (U : unitary (Matrix A A ℂ)) :
    purificationCoefficients ρ U * (purificationCoefficients ρ U)ᴴ = ρ := by
  have hU : (U : Matrix A A ℂ) * (U : Matrix A A ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem U.property
  simp only [purificationCoefficients, Matrix.conjTranspose_mul,
    Cloning.MatrixFidelity.sqrt_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix A A ℂ), hU, Matrix.one_mul,
    Cloning.MatrixFidelity.sqrt_mul_self hρ]

theorem partialTrace_entangledMoment_eq (n : ℕ) (X : Matrix A A ℂ) :
    Cloning.Compression.partialTrace (entangledMoment n X) = tensorPower n (X * Xᴴ) := by
  rw [tensorPower_mul, tensorPower_star]
  rfl

theorem partialTrace_purification_tensor (n : ℕ) (ρ : Matrix A A ℂ)
    (hρ : ρ.PosSemidef) (U : unitary (Matrix A A ℂ)) :
    Cloning.Compression.partialTrace (entangledMoment n (purificationCoefficients ρ U)) =
      tensorPower n ρ := by
  rw [partialTrace_entangledMoment_eq, purificationCoefficients_reduces ρ hρ]

theorem integrable_purification_tensor (n : ℕ) (ρ : Matrix A A ℂ) :
    Integrable (fun U : unitary (Matrix A A ℂ) =>
      entangledMoment n (purificationCoefficients ρ U)) unitaryHaar := by
  have hi := (matrixSandwichCLM (leftTensor n (CFC.sqrt ρ))).integrable_comp
    (integrable_haar_entangledMoment (A := A) n)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro U
  exact (entangledMoment_mul n (CFC.sqrt ρ) (U : Matrix A A ℂ)).symm

theorem trace_tensorPower (n : ℕ) (X : Matrix A A ℂ) :
    Matrix.trace (tensorPower n X) = (Matrix.trace X) ^ n := by
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => X a a)]
  simp

theorem trace_entangledMoment (n : ℕ) (X : Matrix A A ℂ) :
    Matrix.trace (entangledMoment n X) = (Matrix.trace (X * Xᴴ)) ^ n := by
  have ht : Matrix.trace (entangledMoment n X) =
      Matrix.trace (Cloning.Compression.partialTrace (entangledMoment n X)) := by
    simp [Matrix.trace, Matrix.diag, Cloning.Compression.partialTrace, Fintype.sum_prod_type]
  rw [ht, partialTrace_entangledMoment_eq, trace_tensorPower]

theorem trace_purification_tensor (n : ℕ) (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) :
    Matrix.trace (entangledMoment n (purificationCoefficients ρ.matrix U)) = 1 := by
  rw [trace_entangledMoment, purificationCoefficients_reduces _ ρ.positive, ρ.trace_one,
    one_pow]

/-- Each integrand is a normalized pure tensor density matrix. -/
def purificationTensorState (n : ℕ) (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) :
    Cloning.MatrixFidelity.State ((Fin n → A) × (Fin n → A)) where
  matrix := entangledMoment n (purificationCoefficients ρ.matrix U)
  positive := entangledMoment_posSemidef n _
  trace_one := trace_purification_tensor n ρ U

/-- Literal tensor-product coefficients of the rank-one purification
integrands, with the system and environment words grouped separately. -/
theorem purificationTensorState_coefficient (n : ℕ) (ρ : Cloning.MatrixFidelity.State A)
    (U : unitary (Matrix A A ℂ)) (a b c d : Fin n → A) :
    (purificationTensorState n ρ U).matrix (a, b) (c, d) =
      ∏ i, purificationCoefficients ρ.matrix U (a i) (b i) *
        star (purificationCoefficients ρ.matrix U (c i) (d i)) := by
  simp only [purificationTensorState, entangledMoment, entangledTensor, tensorPower,
    star_prod, Finset.prod_mul_distrib]

/-- Exact finite-sample random-purification identity for all positive input
matrices. Both the CPTP map and its Haar moment are explicit constructions. -/
theorem haarPurificationChannel_tensorPower (n : ℕ) (ρ : Matrix A A ℂ)
    (hρ : ρ.PosSemidef) :
    (haarPurificationChannel (A := A) n).toFun (tensorPower n ρ) =
      ∫ U : unitary (Matrix A A ℂ),
        entangledMoment n (purificationCoefficients ρ U) ∂unitaryHaar := by
  rw [haarPurificationChannel_apply]
  have hsquare : tensorPower n ρ = tensorPower n (CFC.sqrt ρ) * tensorPower n (CFC.sqrt ρ) := by
    rw [← tensorPower_mul, Cloning.MatrixFidelity.sqrt_mul_self hρ]
  rw [hsquare, purificationMap_square (haarMoment_posSemidef n) _
    (haarMoment_commute_hermitian n _ (Cloning.MatrixFidelity.sqrt_posSemidef ρ).isHermitian)]
  have hs : (leftTensor n (CFC.sqrt ρ))ᴴ = leftTensor n (CFC.sqrt ρ) := by
    rw [← leftTensor_star, Cloning.MatrixFidelity.sqrt_conjTranspose]
  have h := (matrixSandwichCLM (leftTensor n (CFC.sqrt ρ))).integral_comp_comm
    (integrable_haar_entangledMoment (A := A) n)
  change (∫ U : unitary (Matrix A A ℂ), leftTensor n (CFC.sqrt ρ) *
      entangledMoment n (U : Matrix A A ℂ) * (leftTensor n (CFC.sqrt ρ))ᴴ ∂unitaryHaar) =
    leftTensor n (CFC.sqrt ρ) * haarMoment n * (leftTensor n (CFC.sqrt ρ))ᴴ at h
  change leftTensor n (CFC.sqrt ρ) * haarMoment n * leftTensor n (CFC.sqrt ρ) = _
  rw [hs] at h
  rw [← h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro U
  simpa only [hs] using (entangledMoment_mul n (CFC.sqrt ρ) (U : Matrix A A ℂ)).symm

end Cloning.PCTPurificationChannel
