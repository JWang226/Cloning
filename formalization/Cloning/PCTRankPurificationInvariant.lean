import Cloning.PCTRankPurificationFunctional
import Cloning.PCTPurificationChannelAction

/-! The normalized rectangular Haar moment commutes with every Hermitian
tensor-power input. The environment may have a different dimension. -/

noncomputable section
open scoped BigOperators Classical Matrix Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace Cloning.PCTRankPurification
open Cloning.PCTPurificationChannel Cloning.Compression
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem rectangularLeftTensor_mul (n : ℕ) (X Y : Matrix A A ℂ) :
    rectangularLeftTensor (B := B) n (X * Y) =
      rectangularLeftTensor (B := B) n X * rectangularLeftTensor (B := B) n Y := by
  simp only [rectangularLeftTensor, tensorPower_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]

theorem rectangularLeftTensor_star (n : ℕ) (X : Matrix A A ℂ) :
    rectangularLeftTensor (B := B) n Xᴴ = (rectangularLeftTensor (B := B) n X)ᴴ := by
  simp only [rectangularLeftTensor, tensorPower_star, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

@[simp] theorem rectangularLeftTensor_one (n : ℕ) :
    rectangularLeftTensor (B := B) n (1 : Matrix A A ℂ) = 1 := by
  simp [rectangularLeftTensor, Matrix.one_kronecker_one]

variable [Nonempty A]

theorem rectangularLeftTensor_diagonal (n : ℕ) (z : A → ℂ) :
    rectangularLeftTensor (B := B) n (Matrix.diagonal z) =
      Matrix.diagonal (fun ab : (Fin n → A) × (Fin n → B) => ∏ i, z (ab.1 i)) := by
  rw [rectangularLeftTensor, tensorPower_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_kronecker_diagonal]
  simp

/-- Polynomial uniqueness extends rectangular unitary commutation to every
diagonal matrix, without an environment dimension assumption. -/
theorem rectangular_commute_diagonal_of_commute_unitary (n : ℕ)
    (R : Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ)
    (hR : ∀ V : unitary (Matrix A A ℂ), Commute R (rectangularLeftTensor (B := B) n V.val))
    (z : A → ℂ) : Commute R (rectangularLeftTensor (B := B) n (Matrix.diagonal z)) := by
  rw [rectangularLeftTensor_diagonal]
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
    change R * rectangularLeftTensor (B := B) n (Matrix.diagonal w) =
      rectangularLeftTensor (B := B) n (Matrix.diagonal w) * R at hc
    rw [rectangularLeftTensor_diagonal] at hc
    have he := congrArg (fun M => M ab cd) hc
    simpa [p, q, MvPolynomial.eval_prod, Matrix.mul_diagonal, Matrix.diagonal_mul] using he
  have he := congrArg (MvPolynomial.eval z) hpq
  simpa [p, q, MvPolynomial.eval_prod] using he

theorem rectangular_commute_hermitian_of_commute_unitary (n : ℕ)
    (R : Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ)
    (hR : ∀ V : unitary (Matrix A A ℂ), Commute R (rectangularLeftTensor (B := B) n V.val))
    (X : Matrix A A ℂ) (hX : X.IsHermitian) :
    Commute R (rectangularLeftTensor (B := B) n X) := by
  have hx : X = (hX.eigenvectorUnitary : Matrix A A ℂ) *
      Matrix.diagonal (fun a => (hX.eigenvalues a : ℂ)) *
      (hX.eigenvectorUnitary : Matrix A A ℂ)ᴴ := hX.spectral_theorem
  rw [hx, rectangularLeftTensor_mul, rectangularLeftTensor_mul]
  exact ((hR hX.eigenvectorUnitary).mul_right
    (rectangular_commute_diagonal_of_commute_unitary n R hR _)).mul_right
      (hR (star hX.eigenvectorUnitary))

theorem rectangularHaarMoment_commute_unitary (n : ℕ) (J : Matrix A B ℂ)
    (V : unitary (Matrix A A ℂ)) :
    Commute (rectangularHaarMoment n J) (rectangularLeftTensor (B := B) n V.val) := by
  have hV : V.valᴴ * V.val = 1 := Unitary.star_mul_self_of_mem V.property
  have hn : (rectangularLeftTensor (B := B) n V.val)ᴴ *
      rectangularLeftTensor (B := B) n V.val = 1 := by
    rw [← rectangularLeftTensor_star, ← rectangularLeftTensor_mul,
      hV, rectangularLeftTensor_one]
  have h := congrArg (fun X => X * rectangularLeftTensor (B := B) n V.val)
    (rectangularHaarMoment_unitary_invariant n J V)
  simpa only [Matrix.mul_assoc, hn, Matrix.mul_one] using h.symm

theorem partialTrace_rectangularHaarMoment_commute_unitary (n : ℕ) (J : Matrix A B ℂ)
    (V : unitary (Matrix A A ℂ)) :
    Commute (partialTrace (rectangularHaarMoment n J)) (tensorPower n V.val) := by
  have h := congrArg partialTrace (rectangularHaarMoment_unitary_invariant n J V)
  change partialTrace ((tensorPower n V.val ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ)) *
    rectangularHaarMoment n J *
      (tensorPower n V.val ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ))ᴴ) = _ at h
  rw [partialTrace_tensor_conjugation _ _ _ (by simp)] at h
  have hV : V.valᴴ * V.val = 1 := Unitary.star_mul_self_of_mem V.property
  have hn : (tensorPower n V.val)ᴴ * tensorPower n V.val = 1 := by
    rw [← tensorPower_star, ← tensorPower_mul, hV]
    simp
  have hh := congrArg (fun T => T * tensorPower n V.val) h
  simpa only [Matrix.mul_assoc, hn, Matrix.mul_one] using hh.symm

theorem normalized_rectangularHaarMoment_commute_unitary (n : ℕ) (J : Matrix A B ℂ)
    (V : unitary (Matrix A A ℂ)) :
    Commute (normalizedMoment (rectangularHaarMoment n J)
      (partialTrace_rectangularHaarMoment_posSemidef n J))
      (rectangularLeftTensor (B := B) n V.val) := by
  let H := partialTrace (rectangularHaarMoment n J)
  let hH := partialTrace_rectangularHaarMoment_posSemidef n J
  have hn := momentNormalizer_commutes H hH (tensorPower n V.val)
    (partialTrace_rectangularHaarMoment_commute_unitary n J V).eq
  have hk : Commute (momentNormalizer H hH ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ))
      (rectangularLeftTensor (B := B) n V.val) := by
    show _ * _ = _ * _
    simp only [rectangularLeftTensor, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rw [hn]
  have hstar : (momentNormalizer H hH ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ))ᴴ =
      momentNormalizer H hH ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ) := by
    rw [Matrix.conjTranspose_kronecker, momentNormalizer_star, Matrix.conjTranspose_one]
  unfold normalizedMoment
  change Commute ((_ * rectangularHaarMoment n J) *
    (momentNormalizer H hH ⊗ₖ (1 : Matrix (Fin n → B) (Fin n → B) ℂ))ᴴ) _
  rw [hstar]
  exact (hk.mul_left (rectangularHaarMoment_commute_unitary n J V)).mul_left hk

/-- The actual normalized rectangular moment commutes with every Hermitian
input tensor power. No full-rank or isometric-column assumption on `J` is used. -/
theorem normalized_rectangularHaarMoment_commute_hermitian (n : ℕ) (J : Matrix A B ℂ)
    (X : Matrix A A ℂ) (hX : X.IsHermitian) :
    Commute (normalizedMoment (rectangularHaarMoment n J)
      (partialTrace_rectangularHaarMoment_posSemidef n J))
      (rectangularLeftTensor (B := B) n X) :=
  rectangular_commute_hermitian_of_commute_unitary n _
    (normalized_rectangularHaarMoment_commute_unitary n J) X hX

theorem normalized_rectangularHaarMoment_unitary_invariant (n : ℕ) (J : Matrix A B ℂ)
    (V : unitary (Matrix A A ℂ)) :
    rectangularLeftTensor (B := B) n V *
      normalizedMoment (rectangularHaarMoment n J)
        (partialTrace_rectangularHaarMoment_posSemidef n J) *
      (rectangularLeftTensor (B := B) n V.val)ᴴ =
      normalizedMoment (rectangularHaarMoment n J)
        (partialTrace_rectangularHaarMoment_posSemidef n J) := by
  have hV : V.val * V.valᴴ = 1 := Unitary.mul_star_self_of_mem V.property
  rw [← (normalized_rectangularHaarMoment_commute_unitary n J V).eq,
    Matrix.mul_assoc, ← rectangularLeftTensor_star, ← rectangularLeftTensor_mul,
    hV, rectangularLeftTensor_one, Matrix.mul_one]

end Cloning.PCTRankPurification
