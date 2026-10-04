import Cloning.MatrixFidelity
import Cloning.MatrixFidelityBlocks
import Cloning.Projector
import Cloning.Channels
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic.Ring

/-!
# Concrete operator domination and flat-projector fidelity

These are statements about actual positive complex matrices and the spectral
root-fidelity definition. Fidelity monotonicity is proved using operator
monotonicity of the square root, and flat-projector fidelity is computed by
uniqueness of positive square roots.
-/

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Cloning.MatrixFidelity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The real part of the matrix trace preserves the Loewner order. -/
theorem trace_re_mono {A B : Matrix n n ℂ} (hAB : A ≤ B) :
    (Matrix.trace A).re ≤ (Matrix.trace B).re := by
  have ht := trace_re_nonneg (show (B - A).PosSemidef from hAB)
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using ht

/-- Conjugating both sides by the positive square root preserves order. -/
theorem sandwich_mono {A B : Matrix n n ℂ} (hAB : A ≤ B) (T : Matrix n n ℂ) :
    CFC.sqrt T * A * CFC.sqrt T ≤ CFC.sqrt T * B * CFC.sqrt T := by
  change (CFC.sqrt T * B * CFC.sqrt T - CFC.sqrt T * A * CFC.sqrt T).PosSemidef
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact sandwich_posSemidef (show (B - A).PosSemidef from hAB) T

/-- The precise operator domination step in the projector converse. No
trace normalization is required, so the dominating matrix can have trace > 1. -/
theorem fidelity_mono_left {A B : Matrix n n ℂ} (hAB : A ≤ B) (T : Matrix n n ℂ) :
    fidelity A T ≤ fidelity B T := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  apply trace_re_mono
  exact CFC.sqrt_le_sqrt _ _ (sandwich_mono hAB T)

/-- A positive idempotent matrix is its own positive square root. -/
theorem sqrt_projector {P : Matrix n n ℂ} (hP : P.PosSemidef) (hPP : P * P = P) :
    CFC.sqrt P = P :=
  CFC.sqrt_unique hPP hP.nonneg

/-- Replacing an orthogonal support projection by the identity is a valid
Loewner majorization. -/
theorem projector_le_identity {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (hPP : P * P = P) : P ≤ 1 := by
  apply IsStarProjection.le_one
  exact ⟨hPP, hP.isHermitian⟩

/-- Scaling a positive projector scales its square root by the scalar square root. -/
theorem sqrt_smul_projector {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (hPP : P * P = P) (q : ℝ) (hq : 0 ≤ q) :
    CFC.sqrt (q • P) = Real.sqrt q • P := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, hPP, Real.mul_self_sqrt hq]
  · exact (hP.smul (Real.sqrt_nonneg q)).nonneg

/-- Exact root fidelity between a scalar ambient identity and a flat support
projector. The support rank is represented by `Re (trace P)`. -/
theorem fidelity_identity_projector (c q : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) (hPP : P * P = P) :
    fidelity (c • (1 : Matrix n n ℂ)) (q • P) =
      Real.sqrt (c * q) * (Matrix.trace P).re := by
  unfold fidelity
  rw [sqrt_smul_projector hP hPP q hq]
  have hs : (Real.sqrt q • P) * (c • (1 : Matrix n n ℂ)) * (Real.sqrt q • P) =
      (c * q) • P := by
    rw [smul_mul_smul_comm, Matrix.mul_one, smul_mul_smul_comm, hPP]
    congr 1
    have hsq := Real.mul_self_sqrt hq
    calc
      Real.sqrt q * c * Real.sqrt q = c * (Real.sqrt q * Real.sqrt q) := by ring
      _ = c * q := by rw [hsq]
  rw [hs, sqrt_smul_projector hP hPP (c * q) (mul_nonneg hc hq)]
  simp only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A scalar identity majorant yields the finite flat-projector converse
directly for the concrete root fidelity. -/
theorem fidelity_projector_le_of_identity_bound {A P : Matrix n n ℂ}
    (c q : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hP : P.PosSemidef) (hPP : P * P = P)
    (hA : A ≤ c • (1 : Matrix n n ℂ)) :
    fidelity A (q • P) ≤ Real.sqrt (c * q) * (Matrix.trace P).re := by
  exact (fidelity_mono_left hA (q • P)).trans_eq
    (fidelity_identity_projector c q hc hq hP hPP)

/-- A normalized flat target in a single ambient block gives the precise
dimension-ratio factor occurring in the manuscript. -/
theorem fidelity_flat_projector_block (z q D s : ℝ)
    (hz : 0 ≤ z) (hq : 0 ≤ q) (hD : 0 < D) (hs : 0 < s)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) (hPP : P * P = P)
    (htrace : (Matrix.trace P).re = s) :
    fidelity ((z / D) • (1 : Matrix n n ℂ)) ((q / s) • P) =
      Real.sqrt (z * q / (D / s)) := by
  rw [fidelity_identity_projector (z / D) (q / s)
    (div_nonneg hz hD.le) (div_nonneg hq hs.le) hP hPP, htrace]
  calc
    Real.sqrt ((z / D) * (q / s)) * s =
        (s * 1) * Real.sqrt ((z / (D * 1)) * (q / (s * 1))) := by
      simp only [mul_one, mul_comm]
    _ = Real.sqrt (z * q / (D / s)) :=
      Cloning.Projector.flat_block_root_fidelity z q D s 1 hz hq hD hs zero_lt_one

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- Replacing every input support projector by its ambient identity gives
the positive operator majorant used in the projector converse. -/
theorem flat_projector_blocks_le_majorant
    (P : ∀ i, Matrix (d i) (d i) ℂ) (c : ι → ℝ)
    (hP : ∀ i, (P i).PosSemidef) (hPP : ∀ i, P i * P i = P i)
    (hc : ∀ i, 0 ≤ c i) :
    Matrix.blockDiagonal' (fun i => c i • P i) ≤
      Matrix.blockDiagonal' (fun i => c i • (1 : Matrix (d i) (d i) ℂ)) := by
  change (Matrix.blockDiagonal' (fun i => c i • (1 : Matrix (d i) (d i) ℂ)) -
    Matrix.blockDiagonal' (fun i => c i • P i)).PosSemidef
  rw [← Matrix.blockDiagonal'_sub]
  apply blockDiagonal'_posSemidef
  intro i
  change (c i • (1 : Matrix (d i) (d i) ℂ) - c i • P i).PosSemidef
  rw [← smul_sub]
  exact (show (1 - P i).PosSemidef from projector_le_identity (hP i) (hPP i)).smul (hc i)

/-- The actual matrix trace of the input majorant is the dimension-ratio
moment. Multiplicity dimensions can be included in `D` and `s`. -/
theorem trace_inflated_projector_blocks (p D s : ι → ℝ)
    (hdim : ∀ i, D i = Fintype.card (d i)) :
    (Matrix.trace (Matrix.blockDiagonal' (fun i =>
      (p i / s i) • (1 : Matrix (d i) (d i) ℂ)))).re =
        ∑ i, p i * (D i / s i) := by
  rw [Matrix.trace_blockDiagonal', Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.trace_smul, Matrix.trace_one, Complex.smul_re,
    Complex.natCast_re, smul_eq_mul]
  rw [← hdim i]
  ring

/-- Concrete blockwise projector bound, derived from matrix monotonicity
and the exact direct-sum formula. -/
theorem fidelity_projector_blocks_le
    (A P : ∀ i, Matrix (d i) (d i) ℂ) (c q : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hP : ∀ i, (P i).PosSemidef)
    (hPP : ∀ i, P i * P i = P i)
    (hc : ∀ i, 0 ≤ c i) (hq : ∀ i, 0 ≤ q i)
    (hbound : ∀ i, A i ≤ c i • (1 : Matrix (d i) (d i) ℂ)) :
    fidelity (Matrix.blockDiagonal' A)
      (Matrix.blockDiagonal' (fun i => q i • P i)) ≤
      ∑ i, Real.sqrt (c i * q i) * (Matrix.trace (P i)).re := by
  rw [fidelity_blockDiagonal' A (fun i => q i • P i) hA
    (fun i => (hP i).smul (hq i))]
  apply Finset.sum_le_sum
  intro i _
  exact fidelity_projector_le_of_identity_bound (c i) (q i) (hc i) (hq i)
    (hP i) (hPP i) (hbound i)

/-- The finite projector converse for actual matrices. The output need not
be block diagonal: it is enough that it is dominated by the invariant block
majorant. There is no fidelity-domination hypothesis or assumed fidelity law.

For the physical application, identify `D` with ambient block dimensions;
then `z` is the block trace mass. `s` is the support rank and `M` bounds the
total mass. The theorem also holds for arbitrary positive `D`.
Zero-target blocks can use `q = 0` and any positive-rank projector.
In the manuscript `M` is the input expectation of the dimension ratio. -/
theorem finite_matrix_projector_converse
    (A : Matrix (Sigma d) (Sigma d) ℂ)
    (P : ∀ i, Matrix (d i) (d i) ℂ) (z q D s : ι → ℝ) (M : ℝ)
    (hP : ∀ i, (P i).PosSemidef) (hPP : ∀ i, P i * P i = P i)
    (hz : ∀ i, 0 ≤ z i) (hq : ∀ i, 0 ≤ q i)
    (hD : ∀ i, 0 < D i) (hs : ∀ i, 0 < s i)
    (htrace : ∀ i, (Matrix.trace (P i)).re = s i)
    (hbound : A ≤ Matrix.blockDiagonal' (fun i =>
      (z i / D i) • (1 : Matrix (d i) (d i) ℂ)))
    (hmass : ∑ i, z i ≤ M) :
    fidelity A (Matrix.blockDiagonal' (fun i => (q i / s i) • P i)) ≤
      Real.sqrt (M * ∑ i, q i / (D i / s i)) := by
  have hmono := fidelity_mono_left hbound
    (Matrix.blockDiagonal' (fun i => (q i / s i) • P i))
  rw [fidelity_blockDiagonal'] at hmono
  · have hformula : (∑ i, fidelity ((z i / D i) • (1 : Matrix (d i) (d i) ℂ))
        ((q i / s i) • P i)) = ∑ i, Real.sqrt (z i * q i / (D i / s i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact fidelity_flat_projector_block (z i) (q i) (D i) (s i)
        (hz i) (hq i) (hD i) (hs i) (hP i) (hPP i) (htrace i)
    rw [hformula] at hmono
    exact hmono.trans (Cloning.Projector.block_fidelity_le_of_mass_le
      Finset.univ z q (fun i => D i / s i) M
      (fun i _ => hz i) (fun i _ => hq i)
      (fun i _ => div_pos (hD i) (hs i)) hmass)
  · intro i
    exact Matrix.PosSemidef.one.smul (div_nonneg (hz i) (hD i).le)
  · intro i
    exact (hP i).smul (div_nonneg (hq i) (hs i).le)

end Blocks

section Kraus

variable {κ α β : Type*} [Fintype κ] [Fintype α] [Fintype β]

/-- Positivity of an actual Kraus map gives Loewner monotonicity. -/
theorem krausMap_mono (K : κ → Matrix β α ℂ) {X B : Matrix α α ℂ}
    (hXB : X ≤ B) : Cloning.Channels.krausMap K X ≤ Cloning.Channels.krausMap K B := by
  change (Cloning.Channels.krausMap K B - Cloning.Channels.krausMap K X).PosSemidef
  have hpos := Cloning.Channels.krausMap_positive K
    (show (B - X).PosSemidef from hXB)
  simpa only [Cloning.Channels.krausMap, Matrix.mul_sub, Matrix.sub_mul,
    Finset.sum_sub_distrib] using hpos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- Once the scalar denominator is the ambient dimension, the invariant
majorant's trace is exactly the sum of its block masses. -/
theorem trace_flat_identity_blocks (z D : ι → ℝ)
    (hD : ∀ i, D i ≠ 0) (hdim : ∀ i, D i = Fintype.card (d i)) :
    (Matrix.trace (Matrix.blockDiagonal' (fun i =>
      (z i / D i) • (1 : Matrix (d i) (d i) ℂ)))).re = ∑ i, z i := by
  rw [Matrix.trace_blockDiagonal', Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.trace_smul, Matrix.trace_one, Complex.smul_re,
    Complex.natCast_re, smul_eq_mul]
  rw [← hdim i, div_mul_cancel₀ _ (hD i)]

/-- A finite projector converse for an actual trace-preserving Kraus channel.
The operator majorant and invariant-output decomposition are the remaining
representation-theoretic inputs. Channel positivity, trace preservation,
fidelity monotonicity, direct sums, and the Cauchy--Schwarz bound are proved.

For the manuscript, the input majorant has trace `E R`, so this gives exactly
the square root of the product of the two dimension-ratio moments. -/
theorem finite_kraus_projector_converse [DecidableEq α]
    (K : κ → Matrix (Sigma d) α ℂ) (X B : Matrix α α ℂ)
    (P : ∀ i, Matrix (d i) (d i) ℂ) (z q D s : ι → ℝ)
    (hK : ∑ k, (K k)ᴴ * K k = 1)
    (hXB : X ≤ B)
    (hP : ∀ i, (P i).PosSemidef) (hPP : ∀ i, P i * P i = P i)
    (hz : ∀ i, 0 ≤ z i) (hq : ∀ i, 0 ≤ q i)
    (hD : ∀ i, 0 < D i) (hs : ∀ i, 0 < s i)
    (hdim : ∀ i, D i = Fintype.card (d i))
    (htrace : ∀ i, (Matrix.trace (P i)).re = s i)
    (hinvariant : Cloning.Channels.krausMap K B = Matrix.blockDiagonal'
      (fun i => (z i / D i) • (1 : Matrix (d i) (d i) ℂ))) :
    fidelity (Cloning.Channels.krausMap K X)
      (Matrix.blockDiagonal' (fun i => (q i / s i) • P i)) ≤
      Real.sqrt ((Matrix.trace B).re * ∑ i, q i / (D i / s i)) := by
  apply finite_matrix_projector_converse _ P z q D s (Matrix.trace B).re
    hP hPP hz hq hD hs htrace
  · rw [← hinvariant]
    exact krausMap_mono K hXB
  · have hmass : ∑ i, z i = (Matrix.trace B).re := by
      rw [← trace_flat_identity_blocks z D (fun i => (hD i).ne') hdim,
        ← hinvariant, Cloning.Channels.krausMap_trace K hK B]
    exact hmass.le

end Kraus

end Cloning.MatrixFidelity
