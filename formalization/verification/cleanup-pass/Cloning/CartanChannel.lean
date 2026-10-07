import Cloning.Channels
import Cloning.Compression
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# The Cartan formula is a completely positive trace-preserving map

We construct actual Kraus matrices from the slices of the Cartan inclusion.
The partial-trace balance is the explicit representation-theoretic input needed
for trace preservation; all matrix algebra and complete positivity are proved.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix
namespace Cloning.CartanChannel
open Cloning.Channels Cloning.Compression

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-- A Kraus matrix obtained by contracting the environment leg of the inclusion. -/
def sliceKraus (V : Matrix (A × B) C ℂ) (k : B) : Matrix C A ℂ :=
  fun i j => star (V (j, k) i)

lemma core_eq_kraus (V : Matrix (A × B) C ℂ) (X : Matrix A A ℂ) :
    V.conjTranspose * (X ⊗ₖ (1 : Matrix B B ℂ)) * V = krausMap (sliceKraus V) X := by
  ext i j
  simp only [krausMap, sliceKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, star_star, Finset.sum_mul]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact Finset.sum_comm

/-- The Kraus normalization operator is the environment partial trace. -/
lemma slice_normalization (V : Matrix (A × B) C ℂ) :
    (∑ k, (sliceKraus V k).conjTranspose * sliceKraus V k) =
      partialTrace (V * V.conjTranspose) := by
  ext i j
  simp [sliceKraus, partialTrace, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Scaling all Kraus operators by √r scales the represented map by r. -/
lemma krausMap_sqrt_smul {ι : Type*} [Fintype ι]
    (K : ι → Matrix C A ℂ) (X : Matrix A A ℂ) (r : ℝ) (hr : 0 ≤ r) :
    krausMap (fun i => Real.sqrt r • K i) X = r • krausMap K X := by
  simp only [krausMap, Matrix.conjTranspose_smul, star_trivial]
  simp_rw [(Matrix.smul_mul (R := ℝ)), (Matrix.mul_smul (R := ℝ)), smul_smul, Real.mul_self_sqrt hr]
  exact (Finset.smul_sum ..).symm

/-- Explicit Kraus operators for the Cartan-sector formula. -/
def cartanKraus (V : Matrix (A × B) C ℂ) (din dout : ℝ) (k : B) : Matrix C A ℂ :=
  Real.sqrt (din / dout) • sliceKraus V k

lemma sectorMap_eq_kraus (V : Matrix (A × B) C ℂ) (X : Matrix A A ℂ)
    (din dout : ℝ) (hr : 0 ≤ din / dout) :
    sectorMap din dout V X = krausMap (cartanKraus V din dout) X := by
  rw [sectorMap, core_eq_kraus]
  exact (krausMap_sqrt_smul (sliceKraus V) X (din / dout) hr).symm

/-- The Cartan-sector formula is positive at every finite amplification. -/
lemma sectorMap_completely_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (V : Matrix (A × B) C ℂ) (din dout : ℝ) (hr : 0 ≤ din / dout)
    {X : Matrix (κ × A) (κ × A) ℂ} (hX : X.PosSemidef) :
    (amplify (sectorMap din dout V) X).PosSemidef := by
  have heq : sectorMap din dout V = krausMap (cartanKraus V din dout) := by
    funext Y
    exact sectorMap_eq_kraus V Y din dout hr
  rw [heq]
  exact krausMap_completely_positive _ hX

lemma cartanKraus_normalization (V : Matrix (A × B) C ℂ) (din dout : ℝ)
    (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ)) :
    (∑ k, (cartanKraus V din dout k).conjTranspose * cartanKraus V din dout k) = 1 := by
  have hr : 0 ≤ din / dout := le_of_lt (div_pos hdin hdout)
  simp only [cartanKraus, Matrix.conjTranspose_smul, star_trivial,
    (Matrix.smul_mul (R := ℝ)), (Matrix.mul_smul (R := ℝ)), smul_smul, Real.mul_self_sqrt hr]
  rw [← Finset.smul_sum, slice_normalization, hbalance, smul_smul]
  have hc : din / dout * (dout / din) = 1 := by
    field_simp
  rw [hc, one_smul]

/-- A concrete channel realizing the Cartan formula. The balance identity is
exactly the input supplied by irreducibility and Schur's lemma in the paper. -/
def cartanChannel (V : Matrix (A × B) C ℂ) (din dout : ℝ)
    (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ)) :
    MatrixChannel A C :=
  ofKraus (cartanKraus V din dout) (cartanKraus_normalization V din dout hdin hdout hbalance)

lemma cartanChannel_apply (V : Matrix (A × B) C ℂ) (din dout : ℝ)
    (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ))
    (X : Matrix A A ℂ) :
    (cartanChannel V din dout hdin hdout hbalance).toFun X = sectorMap din dout V X := by
  exact (sectorMap_eq_kraus V X din dout (le_of_lt (div_pos hdin hdout))).symm

end Cloning.CartanChannel
