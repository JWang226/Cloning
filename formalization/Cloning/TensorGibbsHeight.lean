import Cloning.TensorWeightFrameOrthogonal
import Cloning.TensorPBWSpanning
import Cloning.TensorCyclicOccupancy

/-! Exact orthogonal height grading and genuine operator bounds for the
physical sector Gibbs operator. The bounds are derived from computational
support and root weights, with no Gibbs-tail hypothesis. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem cartan_isSymmetric (a : Fin d) : (collectiveGenerator n a a).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪collectiveGenerator n a a x, y⟫_ℂ = ⟪x, collectiveGenerator n a a y⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_right, collectiveGenerator_adjoint]

theorem loweringWord_inner_eq_zero_of_height_ne
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (u v : List (PositiveRoot d)) (huv : loweringHeight u ≠ loweringHeight v) :
    ⟪loweringWord Ω u, loweringWord Ω v⟫_ℂ = 0 := by
  have hw : loweringWeight u ≠ loweringWeight v := by
    intro he
    have hh := loweringWeight_index_sum u
    rw [he, loweringWeight_index_sum v] at hh
    exact huv (by exact_mod_cast hh.symm)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hw
  apply inner_eq_zero_of_real_eigenvalues (collectiveGenerator n a a).toLinearMap
    (cartan_isSymmetric a) _ _ ((mu a : ℝ) + loweringWeight u a)
      ((mu a : ℝ) + loweringWeight v a)
  · simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_intCast] using
      cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight u a
  · simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_intCast] using
      cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight v a
  · intro he
    apply ha
    exact_mod_cast (add_left_cancel he)

theorem cyclicHeightSpace_isOrtho
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    {H J : ℕ} (hHJ : H ≠ J) :
    (cyclicHeightSpace Ω H).IsOrtho (cyclicHeightSpace Ω J) := by
  rw [cyclicHeightSpace, cyclicHeightSpace, Submodule.isOrtho_span]
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  exact loweringWord_inner_eq_zero_of_height_ne Ω mu hweight u v (by simpa [hu, hv] using hHJ)

/-- The actual height subspace inside the cyclic Hilbert space. -/
def sectorHeightSpace (Ω : TensorRegister n (Fin d)) (H : ℕ) : Submodule ℂ (cyclicSector Ω) :=
  (cyclicHeightSpace Ω H).comap (cyclicSector Ω).subtype

theorem sectorHeightSpace_finrank_le (Ω : TensorRegister n (Fin d)) (H : ℕ) :
    Module.finrank ℂ (sectorHeightSpace Ω H) ≤ (H+1)^Fintype.card (PositiveRoot d) := by
  have he := Submodule.comapSubtypeEquivOfLe
    ((cyclicHeightSpace_le_cutoff Ω H).trans (cyclicCutoff_le_cyclicSector Ω _))
  exact he.finrank_eq.trans_le (finrank_cyclicHeightSpace_le_polynomial Ω H)

theorem sectorHeightSpace_orthogonal
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω) :
    OrthogonalFamily ℂ (fun H => sectorHeightSpace Ω H)
      (fun H => (sectorHeightSpace Ω H).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro H J hHJ x hx y hy
  exact cyclicHeightSpace_isOrtho Ω mu hweight hHJ hx y.1 hy

theorem iSup_sectorHeightSpace (Ω : TensorRegister n (Fin d)) :
    (⨆ H : ℕ, sectorHeightSpace Ω H) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hx : x.1 ∈ cyclicSector Ω := x.2
  have hx' : x.1 ∈ ⨆ H : ℕ, cyclicHeightSpace Ω H :=
    (cyclicSector_eq_iSup_cyclicHeightSpace Ω).le hx
  have hm : (⨆ H : ℕ, cyclicHeightSpace Ω H) ≤
      (⨆ H : ℕ, sectorHeightSpace Ω H).map (cyclicSector Ω).subtype := by
    apply iSup_le
    intro H y hy
    refine ⟨⟨y, (cyclicCutoff_le_cyclicSector Ω _) (cyclicHeightSpace_le_cutoff Ω H hy)⟩, ?_, rfl⟩
    exact (le_iSup (fun H => sectorHeightSpace Ω H) H) hy
  obtain ⟨y, hy, he⟩ := hm hx'
  have hyx : y = x := Subtype.ext he
  simpa only [hyx] using hy

def tensorWordMultiplier (p : Fin d → ℝ) (v : Fin n → Fin d) : ℝ := ∏ t, p (v t)

theorem tensorWordMultiplier_loweringWord
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (w : List (PositiveRoot d))
    (v : Fin n → Fin d) (hv : loweringWord Ω w v ≠ 0) :
    tensorWordMultiplier p v = (∏ a, p a ^ mu a) * wordBoltzmann p w := by
  have he := congrArg (fun x : TensorRegister n (Fin d) => x v)
    (tensorOperator_diagonal_loweringWord Ω mu hweight p hp w)
  simp only [tensorOperator_diagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at he
  apply Complex.ofReal_injective
  simpa only [tensorWordMultiplier, Complex.ofReal_prod] using mul_right_cancel₀ hv he

/-- Outside the finite-height Boltzmann bound every computational coefficient
of the whole height space vanishes, not only those of a preferred word family. -/
theorem cyclicHeightSpace_coefficient_bound
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (θ : ℝ) (hθ : 0 ≤ θ)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height)
    (H : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicHeightSpace Ω H)
    (v : Fin n → Fin d)
    (hv : (∏ a, p a ^ mu a) * θ^H < tensorWordMultiplier p v) : x v = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    by_contra hn
    have he := tensorWordMultiplier_loweringWord Ω mu hweight p hp w v hn
    have hb : (∏ a, p a ^ mu a) * wordBoltzmann p w ≤
        (∏ a, p a ^ mu a) * θ ^ loweringHeight w := mul_le_mul_of_nonneg_left
      (wordBoltzmann_le_pow_height p (fun a => (hp a).le) θ hθ hroot w)
      (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a).le (mu a)))
    rw [hw, ← he] at hb
    exact (not_lt_of_ge hb) hv
  | zero => rfl
  | add x y hx hy ihx ihy => simp [lp.coeFn_add, ihx, ihy]
  | smul c x hx ih => simp [lp.coeFn_smul, ih]

theorem tensorOperator_diagonal_norm_le_on_height
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (θ : ℝ) (hθ : 0 ≤ θ)
    (hroot : ∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height)
    (H : ℕ) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicHeightSpace Ω H) :
    ‖tensorOperator n (Matrix.diagonal (fun a => (p a : ℂ))) x‖ ≤
      ((∏ a, p a ^ mu a) * θ^H) * ‖x‖ := by
  apply register_norm_le_of_pointwise _ x _
    (mul_nonneg (Finset.prod_nonneg (fun a _ => pow_nonneg (hp a).le (mu a))) (pow_nonneg hθ H))
  intro v
  rw [tensorOperator_diagonal_apply, norm_mul]
  by_cases hv : x v = 0
  · simp [hv]
  · have hb : tensorWordMultiplier p v ≤ (∏ a, p a ^ mu a) * θ^H := by
      by_contra! hh
      exact hv (cyclicHeightSpace_coefficient_bound Ω mu hweight p hp θ hθ hroot H hx v hh)
    have hn : ‖∏ t, (p (v t) : ℂ)‖ = tensorWordMultiplier p v := by
      rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun t _ => (hp (v t)).le))]
      rfl
    rw [hn]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

end Cloning.TensorLie
