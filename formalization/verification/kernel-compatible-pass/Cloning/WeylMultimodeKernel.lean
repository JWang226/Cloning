import Cloning.WeylKernel
import Cloning.MultimodeCoherent

/-! Exact Weyl phases and coherent kernels for finitely many bosonic modes. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The joint Weyl phase is the product of the individual mode phases. -/
def displacementPhase {d : ℕ} (a z : Fin d → ℂ) : ℂ :=
  ∏ i, ComplexCoherent.displacementPhase (a i) (z i)

/-- The coherent action prescribed by simultaneous displacement of all modes. -/
def displacedCoherent {d : ℕ} (a z : Fin d → ℂ) : Fock d :=
  displacementPhase a z • coherentVector (a + z)

@[simp] theorem displacementPhase_norm {d : ℕ} (a z : Fin d → ℂ) :
    ‖displacementPhase a z‖ = 1 := by
  simp only [displacementPhase, norm_prod, ComplexCoherent.displacementPhase_norm,
    Finset.prod_const_one]

@[simp] theorem displacementPhase_zero_left {d : ℕ} (z : Fin d → ℂ) :
    displacementPhase 0 z = 1 := by
  simp [displacementPhase]

@[simp] theorem displacementPhase_zero_right {d : ℕ} (a : Fin d → ℂ) :
    displacementPhase a 0 = 1 := by
  simp [displacementPhase]

/-- The full complex coherent kernel is preserved jointly in all modes. -/
theorem inner_displacedCoherent {d : ℕ} (a z w : Fin d → ℂ) :
    ⟪displacedCoherent a z, displacedCoherent a w⟫_ℂ =
      ⟪coherentVector z, coherentVector w⟫_ℂ := by
  have hsingle (i : Fin d) := ComplexCoherent.inner_displacedCoherent (a i) (z i) (w i)
  simp only [ComplexCoherent.displacedCoherent, inner_smul_left, inner_smul_right] at hsingle
  simp only [displacedCoherent, inner_smul_left, inner_smul_right, displacementPhase,
    coherentVector, inner_tensorVector, map_prod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact hsingle i

/-- The finite-mode Weyl cocycle is inherited from the one-mode cocycles. -/
theorem displacementPhase_cocycle {d : ℕ} (a b z : Fin d → ℂ) :
    displacementPhase b z * displacementPhase a (b + z) =
      displacementPhase a b * displacementPhase (a + b) z := by
  simp only [displacementPhase, Pi.add_apply, ← Finset.prod_mul_distrib,
    ComplexCoherent.displacementPhase_cocycle]

/-- Finite multimode coherent superpositions. -/
def coherentCombination {d : ℕ} : ((Fin d → ℂ) →₀ ℂ) →ₗ[ℂ] Fock d :=
  Finsupp.linearCombination ℂ coherentVector

def displacedCombination {d : ℕ} (a : Fin d → ℂ) :
    ((Fin d → ℂ) →₀ ℂ) →ₗ[ℂ] Fock d :=
  Finsupp.linearCombination ℂ (displacedCoherent a)

/-- The prescribed action preserves inner products of arbitrary finite
superpositions, so it respects all linear relations between coherent vectors. -/
theorem inner_displacedCombination {d : ℕ} (a : Fin d → ℂ)
    (c e : (Fin d → ℂ) →₀ ℂ) :
    ⟪displacedCombination a c, displacedCombination a e⟫_ℂ =
      ⟪coherentCombination c, coherentCombination e⟫_ℂ := by
  simp only [displacedCombination, coherentCombination, Finsupp.linearCombination_apply,
    Finsupp.sum, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    inner_displacedCoherent]

theorem norm_displacedCombination {d : ℕ} (a : Fin d → ℂ)
    (c : (Fin d → ℂ) →₀ ℂ) :
    ‖displacedCombination a c‖ = ‖coherentCombination c‖ := by
  have h := congrArg (fun z : ℂ => z.re) (inner_displacedCombination a c c)
  change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _ at h
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  nlinarith [norm_nonneg (displacedCombination a c), norm_nonneg (coherentCombination c)]

end Cloning.MultimodeCoherent
