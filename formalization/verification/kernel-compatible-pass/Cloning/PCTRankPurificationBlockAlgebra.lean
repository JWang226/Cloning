import Cloning.PCTRankPurificationFunctional

/-! Finite rectangular block algebra for the literal rank-purification
normalizer. These identities retain every multiplicity copy separately. -/
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace Cloning.PCTRankPurification
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A B C I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq I]

/-- Spectral functions act by their eigenvalue on a rectangular isometric
block, even when the ambient positive matrix has a kernel. -/
theorem momentSpectral_mul_isometry (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (E : Matrix A B ℂ) (hE : Eᴴ*E=1) (c : ℝ)
    (hHE : H*E=(c : ℂ) • E) (f : ℝ → ℂ) :
    momentSpectral H hH f*E=f c • E := by
  have hP : H*(E*Eᴴ)=(c : ℂ) • (E*Eᴴ) := by
    rw [← Matrix.mul_assoc,hHE,Matrix.smul_mul]
  have hh := congrArg (fun M : Matrix A A ℂ => M*E)
    (momentSpectral_left_eigenrelation H hH f (E*Eᴴ) c hP)
  simpa only [Matrix.mul_assoc,hE,Matrix.mul_one,Matrix.smul_mul] using hh

theorem momentNormalizer_mul_isometry (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (E : Matrix A B ℂ) (hE : Eᴴ*E=1) (c : ℝ) (hHE : H*E=(c : ℂ) • E) :
    momentNormalizer H hH*E=((Real.sqrt c)⁻¹ : ℂ) • E :=
  momentSpectral_mul_isometry H hH E hE c hHE (fun t => ((Real.sqrt t)⁻¹ : ℂ))

theorem momentSupport_mul_isometry (H : Matrix A A ℂ) (hH : H.PosSemidef)
    (E : Matrix A B ℂ) (hE : Eᴴ*E=1) (c : ℝ) (hc : 0<c)
    (hHE : H*E=(c : ℂ) • E) : momentSupport H hH*E=E := by
  have hh := momentSpectral_mul_isometry H hH E hE c hHE (fun t => if t=0 then 0 else 1)
  simpa only [momentSupport,momentSpectral,if_neg hc.ne',one_smul] using hh

/-- Positive scalar block weights give literal eigenrelations for the full
ambient matrix, without any spanning requirement on the ambient blocks. -/
theorem sum_weighted_projectors_mul {J : I → Type*} [∀ i,Fintype (J i)] [∀ i,DecidableEq (J i)]
    (E : ∀ i,Matrix A (J i) ℂ) (hE : ∀ i,(E i)ᴴ*E i=1)
    (horth : ∀ i j,i≠j → (E i)ᴴ*E j=0) (c : I → ℂ) (j : I) :
    (∑ i,c i • (E i*(E i)ᴴ))*E j=c j • E j := by
  rw [Matrix.sum_mul]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.smul_mul,Matrix.mul_assoc,hE,Matrix.mul_one]
  · intro i hi hij
    rw [Matrix.smul_mul,Matrix.mul_assoc,horth i j hij,Matrix.mul_zero,smul_zero]
  · simp

/-- Transport a complete input block resolution through any rectangular
map; no orthogonality on the larger ambient space is assumed here. -/
theorem conjugated_identity_resolution {J : I → Type*} [∀ i,Fintype (J i)] [∀ i,DecidableEq (J i)]
    (F : ∀ i,Matrix B (J i) ℂ) (hF : ∑ i,F i*(F i)ᴴ=1) (K : Matrix A B ℂ) :
    K*Kᴴ=∑ i,(K*F i)*(K*F i)ᴴ := by
  calc
    _ = K*(∑ i,F i*(F i)ᴴ)*Kᴴ := by rw [hF,Matrix.mul_one]
    _ = _ := by
      rw [Matrix.mul_sum,Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- Rectangular conjugation as a continuous linear map, for exact Bochner
transport of the actual sector Haar integrals. -/
def rectangularSandwichCLM (E : Matrix A B ℂ) : Matrix B B ℂ →L[ℂ] Matrix A A ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => E*X*Eᴴ
      map_add' := by intro X Y; simp only [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intro c X; simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }

end Cloning.PCTRankPurification
