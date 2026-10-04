import Cloning.TensorGibbsWeights
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! Orthogonalization of the actual physical word families preserves every
exact real Cartan or Gibbs eigenvalue. Distinct-weight blocks cannot mix in
Gram–Schmidt, even when several root occupations have the same weight. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

theorem inner_eq_zero_of_real_eigenvalues (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (x y : H) (a b : ℝ) (hx : T x = (a : ℂ) • x) (hy : T y = (b : ℂ) • y)
    (hab : a ≠ b) : ⟪x,y⟫_ℂ = 0 := by
  have he := hT x y
  rw [hx, hy, inner_smul_left, inner_smul_right] at he
  simp only [Complex.conj_ofReal] at he
  by_contra hxy
  exact hab (by exact_mod_cast mul_right_cancel₀ hxy he)

theorem gramSchmidt_real_eigenvector (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (f : ι → H) (a : ι → ℝ) (hf : ∀ i, T (f i) = (a i : ℂ) • f i) (i : ι) :
    T (gramSchmidt ℂ f i) = (a i : ℂ) • gramSchmidt ℂ f i := by
  refine (wellFounded_lt (α := ι)).induction
    (C := fun j : ι => T (gramSchmidt ℂ f j) = (a j : ℂ) • gramSchmidt ℂ f j) i ?_
  intro i ih
  rw [gramSchmidt_def]
  simp only [map_sub, map_sum, smul_sub, Finset.smul_sum, hf]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < i := Finset.mem_Iio.mp hj
  rw [Submodule.starProjection_singleton]
  by_cases he : a j = a i
  · rw [map_smul, ih j hj', he]
    simp only [smul_smul, mul_comm]
  · have hz := inner_eq_zero_of_real_eigenvalues T hT (gramSchmidt ℂ f j) (f i)
      (a j) (a i) (ih j hj') (hf i) he
    simp only [hz, zero_div, zero_smul, smul_zero, map_zero]

theorem gramSchmidtNormed_real_eigenvector (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (f : ι → H) (a : ι → ℝ) (hf : ∀ i, T (f i) = (a i : ℂ) • f i) (i : ι) :
    T (gramSchmidtNormed ℂ f i) = (a i : ℂ) • gramSchmidtNormed ℂ f i := by
  rw [gramSchmidtNormed, map_smul, gramSchmidt_real_eigenvector T hT f a hf]
  simp only [smul_smul, mul_comm]

end Abstract

variable {n d : ℕ} {ι : Type*}
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- Every simultaneous physical Cartan eigenvalue is retained exactly by
the common orthonormalization, including all weight multiplicities. -/
theorem gramSchmidtNormed_cartan
    (f : ι → TensorRegister n (Fin d)) (κ : ι → Fin d → ℝ)
    (hf : ∀ i a, collectiveGenerator n a a (f i) = (κ i a : ℂ) • f i)
    (i : ι) (a : Fin d) :
    collectiveGenerator n a a (gramSchmidtNormed ℂ f i) =
      (κ i a : ℂ) • gramSchmidtNormed ℂ f i := by
  apply gramSchmidtNormed_real_eigenvector (collectiveGenerator n a a).toLinearMap
    _ f (fun i => κ i a) (fun i => hf i a) i
  intro x y
  change ⟪collectiveGenerator n a a x, y⟫_ℂ = ⟪x, collectiveGenerator n a a y⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_right, collectiveGenerator_adjoint]

/-- The exact Cartan labels of physical lowering words survive Gram–Schmidt. -/
theorem gramSchmidtNormed_loweringWord_cartan
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (w : ι → List (PositiveRoot d)) (i : ι) (a : Fin d) :
    collectiveGenerator n a a (gramSchmidtNormed ℂ (fun j => loweringWord Ω (w j)) i) =
      ((mu a : ℂ) + (loweringWeight (w i) a : ℂ)) •
        gramSchmidtNormed ℂ (fun j => loweringWord Ω (w j)) i := by
  have h := gramSchmidtNormed_cartan (fun j => loweringWord Ω (w j))
    (fun j a => (mu a : ℝ) + loweringWeight (w j) a) (fun j a => by
      simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_intCast] using
        cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight (w j) a) i a
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_intCast] using h

end Cloning.TensorLie
