import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact matrix algebra for rank compression

This file formalizes the algebraic insertion step in `channel-compression` of
`cloning.tex`, using actual finite complex matrices and their conjugate transposes.
The isometries and the Cartan restriction identity are explicit hypotheses.
Their existence and the representation-theoretic proof of the restriction
identity are outside this file. There is no hypothesis asserting the compression
conclusion and no abstract axiom about quantum channels or fidelity.
-/

noncomputable section
open scoped Matrix Kronecker
namespace Cloning.Compression

set_option linter.unusedSectionVars false

variable {A B C a b c : Type*}
variable [Fintype A] [Fintype B] [Fintype C]
variable [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Compressing an embedded operator back through an isometry recovers it. -/
lemma isometry_compress (J : Matrix A a ℂ) (X : Matrix a a ℂ)
    (hJ : J.conjTranspose * J = 1) :
    J.conjTranspose * (J * X * J.conjTranspose) * J = X := by
  calc
    _ = (J.conjTranspose * J) * X * (J.conjTranspose * J) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hJ]; simp

/-- The tensor-factor simplification used in rank compression. -/
lemma tensor_compression (Ja : Matrix A a ℂ) (Jb : Matrix B b ℂ)
    (X : Matrix a a ℂ)
    (ha : Ja.conjTranspose * Ja = 1)
    (hb : Jb.conjTranspose * Jb = 1) :
    (Ja ⊗ₖ Jb).conjTranspose *
      ((Ja * X * Ja.conjTranspose) ⊗ₖ (1 : Matrix B B ℂ)) * (Ja ⊗ₖ Jb) =
        X ⊗ₖ (1 : Matrix b b ℂ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  rw [isometry_compress Ja X ha]
  simp [hb]

/-- Algebraic consequence of the Cartan restriction identity `Vd Jc = (Ja ⊗ Jb) Vr`.
This is the unscaled channel-compression identity. -/
lemma cartan_compression (Ja : Matrix A a ℂ) (Jb : Matrix B b ℂ)
    (Jc : Matrix C c ℂ) (Vd : Matrix (A × B) C ℂ) (Vr : Matrix (a × b) c ℂ)
    (X : Matrix a a ℂ)
    (ha : Ja.conjTranspose * Ja = 1)
    (hb : Jb.conjTranspose * Jb = 1)
    (hrestriction : Vd * Jc = (Ja ⊗ₖ Jb) * Vr) :
    Jc.conjTranspose *
      (Vd.conjTranspose * ((Ja * X * Ja.conjTranspose) ⊗ₖ (1 : Matrix B B ℂ)) * Vd)
      * Jc = Vr.conjTranspose * (X ⊗ₖ (1 : Matrix b b ℂ)) * Vr := by
  calc
    _ = (Vd * Jc).conjTranspose *
        ((Ja * X * Ja.conjTranspose) ⊗ₖ (1 : Matrix B B ℂ)) * (Vd * Jc) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((Ja ⊗ₖ Jb) * Vr).conjTranspose *
        ((Ja * X * Ja.conjTranspose) ⊗ₖ (1 : Matrix B B ℂ)) *
        ((Ja ⊗ₖ Jb) * Vr) := by rw [hrestriction]
    _ = Vr.conjTranspose *
        ((Ja ⊗ₖ Jb).conjTranspose *
          ((Ja * X * Ja.conjTranspose) ⊗ₖ (1 : Matrix B B ℂ)) * (Ja ⊗ₖ Jb)) * Vr := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [tensor_compression Ja Jb X ha hb]

/-- The dimension-ratio coefficient in the paper. -/
lemma dimension_ratio_identity (ad bd ar br : ℝ)
    (hbd : bd ≠ 0) (har : ar ≠ 0) (hbr : br ≠ 0) :
    ad / bd = ((ad / ar) / (bd / br)) * (ar / br) := by
  field_simp

/-- The explicit Cartan-channel formula, before any channel-property assertions. -/
def sectorMap (din dout : ℝ) (V : Matrix (A × B) C ℂ) (X : Matrix A A ℂ) :
    Matrix C C ℂ :=
  (din / dout) • (V.conjTranspose * (X ⊗ₖ (1 : Matrix B B ℂ)) * V)

/-- Exact rank compression including the paper's coefficient `Rμ/Rν`. -/
lemma sectorMap_compression (Ja : Matrix A a ℂ) (Jb : Matrix B b ℂ)
    (Jc : Matrix C c ℂ) (Vd : Matrix (A × B) C ℂ) (Vr : Matrix (a × b) c ℂ)
    (X : Matrix a a ℂ) (ad bd ar br : ℝ)
    (ha : Ja.conjTranspose * Ja = 1)
    (hb : Jb.conjTranspose * Jb = 1)
    (hrestriction : Vd * Jc = (Ja ⊗ₖ Jb) * Vr)
    (hbd : bd ≠ 0) (har : ar ≠ 0) (hbr : br ≠ 0) :
    Jc.conjTranspose * sectorMap ad bd Vd (Ja * X * Ja.conjTranspose) * Jc =
      ((ad / ar) / (bd / br)) • sectorMap ar br Vr X := by
  simp only [sectorMap, Matrix.mul_smul, Matrix.smul_mul]
  rw [cartan_compression Ja Jb Jc Vd Vr X ha hb hrestriction]
  rw [smul_smul, dimension_ratio_identity ad bd ar br hbd har hbr]

/-- Re-embedding the compressed block gives precisely the supported channel
identity in equation `channel-compression`. -/
lemma sectorMap_supported_compression (Ja : Matrix A a ℂ) (Jb : Matrix B b ℂ)
    (Jc : Matrix C c ℂ) (Vd : Matrix (A × B) C ℂ) (Vr : Matrix (a × b) c ℂ)
    (X : Matrix a a ℂ) (ad bd ar br : ℝ)
    (ha : Ja.conjTranspose * Ja = 1)
    (hb : Jb.conjTranspose * Jb = 1)
    (hrestriction : Vd * Jc = (Ja ⊗ₖ Jb) * Vr)
    (hbd : bd ≠ 0) (har : ar ≠ 0) (hbr : br ≠ 0) :
    (Jc * Jc.conjTranspose) * sectorMap ad bd Vd (Ja * X * Ja.conjTranspose) *
      (Jc * Jc.conjTranspose) =
      ((ad / ar) / (bd / br)) • (Jc * sectorMap ar br Vr X * Jc.conjTranspose) := by
  calc
    _ = Jc * (Jc.conjTranspose * sectorMap ad bd Vd
        (Ja * X * Ja.conjTranspose) * Jc) * Jc.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [sectorMap_compression Ja Jb Jc Vd Vr X ad bd ar br ha hb
        hrestriction hbd har hbr]
      simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The support operator is an orthogonal projection for an isometric inclusion. -/
lemma support_projection (J : Matrix A a ℂ) (hJ : J.conjTranspose * J = 1) :
    (J * J.conjTranspose).conjTranspose = J * J.conjTranspose ∧
      (J * J.conjTranspose) * (J * J.conjTranspose) = J * J.conjTranspose := by
  constructor
  · simp
  · calc
      _ = J * (J.conjTranspose * J) * J.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ]; simp

/-- Trace is preserved by an isometric embedding. This is the normalization
step after Schur--Weyl naturality identifies the unnormalized support blocks. -/
lemma trace_isometric_embedding (J : Matrix A a ℂ) (X : Matrix a a ℂ)
    (hJ : J.conjTranspose * J = 1) :
    Matrix.trace (J * X * J.conjTranspose) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle, hJ, Matrix.one_mul]

/-- Algebraic normalization by trace (defined also at trace zero). -/
def normalize (X : Matrix A A ℂ) : Matrix A A ℂ :=
  (Matrix.trace X)⁻¹ • X

/-- The conditional-support identity after dividing the representation blocks
by their Schur-polynomial traces. -/
lemma normalize_isometric_embedding (J : Matrix A a ℂ) (X : Matrix a a ℂ)
    (hJ : J.conjTranspose * J = 1) :
    normalize (J * X * J.conjTranspose) = J * normalize X * J.conjTranspose := by
  simp only [normalize, trace_isometric_embedding J X hJ,
    Matrix.mul_smul, Matrix.smul_mul]

/-- The Cartan formula sends the maximally mixed input to the maximally mixed
output whenever its defining inclusion is isometric. -/
lemma sectorMap_maximally_mixed (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (hdin : din ≠ 0) (hV : V.conjTranspose * V = 1) :
    sectorMap din dout V ((1 / din) • (1 : Matrix A A ℂ)) =
      (1 / dout) • (1 : Matrix C C ℂ) := by
  unfold sectorMap
  rw [Matrix.smul_kronecker, Matrix.one_kronecker_one, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hV, smul_smul]
  congr 1
  field_simp

/-- Partial trace over the second finite matrix index. -/
def partialTrace (Y : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun i j => ∑ k, Y (i, k) (j, k)

/-- Defining trace-pairing identity for the finite-dimensional partial trace. -/
lemma trace_tensor_pairing (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace ((X ⊗ₖ (1 : Matrix B B ℂ)) * Y) =
      Matrix.trace (X * partialTrace Y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, partialTrace, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- The partial-trace balance obtained from Schur's lemma implies trace
preservation of the explicit Cartan-sector formula. -/
lemma sectorMap_trace_preserving (V : Matrix (A × B) C ℂ)
    (X : Matrix A A ℂ) (din dout : ℝ) (hdin : din ≠ 0) (hdout : dout ≠ 0)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ)) :
    Matrix.trace (sectorMap din dout V X) = Matrix.trace X := by
  unfold sectorMap
  rw [Matrix.trace_smul, Matrix.trace_mul_cycle]
  rw [Matrix.trace_mul_comm]
  rw [trace_tensor_pairing, hbalance, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_smul]
  have hcoef : din / dout * (dout / din) = 1 := by field_simp
  rw [hcoef, one_smul]

end Cloning.Compression
