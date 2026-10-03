import Cloning.CoherentKernel
import Mathlib.Analysis.Normed.Operator.Extend

/-! The coherent-vector action and cocycle of Weyl displacements, obtained
from the proved Fock-space overlap kernel. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Phase in the displacement action `D(a)|z⟩`. -/
def displacementPhase (a z : ℂ) : ℂ :=
  Complex.exp ((a * starRingEnd ℂ z - starRingEnd ℂ a * z) / 2)

/-- The prescribed translated coherent vector. -/
def displacedCoherent (a z : ℂ) : Fock :=
  displacementPhase a z • coherentVector (a + z)

lemma norm_sq_cast (z : ℂ) : (‖z‖ ^ 2 : ℂ) = starRingEnd ℂ z * z := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

lemma norm_sq_cast' (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

@[simp] theorem displacementPhase_norm (a z : ℂ) : ‖displacementPhase a z‖ = 1 := by
  rw [displacementPhase, Complex.norm_exp]
  have h : ((a * starRingEnd ℂ z - starRingEnd ℂ a * z) / 2).re = 0 := by
    simp [Complex.mul_re, Complex.div_ofNat_re]
  rw [h, Real.exp_zero]

@[simp] theorem displacementPhase_zero_left (z : ℂ) : displacementPhase 0 z = 1 := by
  simp [displacementPhase]

@[simp] theorem displacementPhase_zero_right (a : ℂ) : displacementPhase a 0 = 1 := by
  simp [displacementPhase]

/-- Translating and phasing the coherent vectors preserves their full complex
inner products, not only their overlap modulus. -/
theorem inner_displacedCoherent (a z w : ℂ) :
    ⟪displacedCoherent a z, displacedCoherent a w⟫_ℂ =
      ⟪coherentVector z, coherentVector w⟫_ℂ := by
  simp only [displacedCoherent, inner_smul_left, inner_smul_right,
    displacementPhase, inner_coherentVector, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_div₀, map_sub, map_mul, map_ofNat, starRingEnd_self_apply,
    map_add, norm_sq_cast]
  ring

/-- The Weyl phase obeys the translation cocycle. -/
theorem displacementPhase_cocycle (a b z : ℂ) :
    displacementPhase b z * displacementPhase a (b + z) =
      displacementPhase a b * displacementPhase (a + b) z := by
  simp only [displacementPhase, ← Complex.exp_add, map_add]
  congr 1
  ring

/-- The finite linear combinations used to construct Weyl operators. -/
def coherentCombination : (ℂ →₀ ℂ) →ₗ[ℂ] Fock :=
  Finsupp.linearCombination ℂ coherentVector

def displacedCombination (a : ℂ) : (ℂ →₀ ℂ) →ₗ[ℂ] Fock :=
  Finsupp.linearCombination ℂ (displacedCoherent a)

/-- Exact kernel equality controls arbitrary finite superpositions. -/
theorem inner_displacedCombination (a : ℂ) (c d : ℂ →₀ ℂ) :
    ⟪displacedCombination a c, displacedCombination a d⟫_ℂ =
      ⟪coherentCombination c, coherentCombination d⟫_ℂ := by
  simp only [displacedCombination, coherentCombination, Finsupp.linearCombination_apply,
    Finsupp.sum, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    inner_displacedCoherent]

theorem norm_displacedCombination (a : ℂ) (c : ℂ →₀ ℂ) :
    ‖displacedCombination a c‖ = ‖coherentCombination c‖ := by
  have h := congrArg (fun z : ℂ => z.re) (inner_displacedCombination a c c)
  change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _ at h
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  nlinarith [norm_nonneg (displacedCombination a c), norm_nonneg (coherentCombination c)]

end Cloning.ComplexCoherent
