import Cloning.PCTFlatGaussianCrossFrameExistence
import Cloning.PCTGaussianCovarianceClassical

/-! The actual reduced differential at a flat state has exactly the
Hermitian real-coordinate cross kernel used in the purity Gaussian integral. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTFlatGaussianCross
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A] {s : ℕ}

lemma coefficientVector_inner_trace (M N : Matrix A A ℂ) (hM : M.IsHermitian) :
    ⟪coefficientVector M,coefficientVector N⟫_ℂ=Matrix.trace (M*N) := by
  rw [coefficientVector_inner]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hh := congrArg (fun X : Matrix A A ℂ => X a b) hM
  change star (M b a)=M a b at hh
  rw [hh]

lemma frameTangent_inner
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A))) (z w : Fin s → ℂ) :
    ⟪frameTangent u z,frameTangent u w⟫_ℂ=∑ i,star (z i)*w i := by
  have hu : Orthonormal ℂ (fun i : Fin s => u i.succ) :=
    u.orthonormal.comp _ (Fin.succ_injective _)
  simpa [frameTangent] using hu.inner_sum z w Finset.univ

/-- In an actual Hermitian frame the reduced differential retains precisely
its real tangent coordinates, with the derived factor `2 sqrt(c)`. -/
theorem flatDifferential_frame_coefficients
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hu : ∀ i a b,star (u i (b,a))=u i (a,b))
    (c : ℝ) (z : Fin s → ℂ) :
    coefficientVector (partialTraceDifferential (fun _ : A => c) (frameTangentMatrix u z))=
      frameTangent u (fun i => ((2*Real.sqrt c*(z i).re : ℝ) : ℂ)) := by
  ext ab
  rcases ab with ⟨a,b⟩
  simp only [coefficientVector_apply,partialTraceDifferential_apply,
    frameTangentMatrix,frameTangent,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,star_sum,star_mul,hu,Finset.sum_mul,Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hz := Complex.add_conj (z i)
  change z i+star (z i)=((2*(z i).re : ℝ) : ℂ) at hz
  calc
    _=(Real.sqrt c : ℂ)*(z i+star (z i))*u i.succ (a,b) := by ring
    _=((2*Real.sqrt c*(z i).re : ℝ) : ℂ)*u i.succ (a,b) := by
      rw [hz]
      push_cast
      ring

/-- Exact matrix trace kernel at an arbitrary constant diagonal reference. -/
theorem flatDifferential_trace_cross
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hu : ∀ i a b,star (u i (b,a))=u i (a,b))
    (c : ℝ) (hc : 0≤c) (z w : Fin s → ℂ) :
    (Matrix.trace (partialTraceDifferential (fun _ : A => c) (frameTangentMatrix u z) *
      partialTraceDifferential (fun _ : A => c) (frameTangentMatrix u w))).re=
        4*c*∑ i,(z i).re*(w i).re := by
  rw [← coefficientVector_inner_trace _ _ (partialTraceDifferential_hermitian _ _),
    flatDifferential_frame_coefficients u hu,flatDifferential_frame_coefficients u hu,
    frameTangent_inner]
  simp only [Complex.re_sum,Complex.conj_ofReal,Complex.star_def,
    ← Complex.ofReal_mul,Complex.ofReal_re,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=4*(Real.sqrt c)^2*((z i).re*(w i).re) := by ring
    _=_ := by rw [Real.sq_sqrt hc]

/-- The physical flat-state normalization cancels exactly against rank. -/
theorem flatDifferential_rank_trace_cross
    (u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)))
    (hu : ∀ i a b,star (u i (b,a))=u i (a,b))
    (r : ℕ) (hr : 0<r) (z w : Fin s → ℂ) :
    (r : ℝ)*(Matrix.trace
      (partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u z) *
       partialTraceDifferential (fun _ : A => (r : ℝ)⁻¹) (frameTangentMatrix u w))).re=
        4*∑ i,(z i).re*(w i).re := by
  rw [flatDifferential_trace_cross u hu _ (by positivity)]
  have hR : (r : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  field_simp

end Cloning.PCTFlatGaussianCross
