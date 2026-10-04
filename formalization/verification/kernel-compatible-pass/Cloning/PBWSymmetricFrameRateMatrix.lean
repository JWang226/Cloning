import Cloning.PBWSymmetricFrameRate
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! The polar construction is exactly the manuscript's matrix formula
`(v_i) (sqrt(Gram(v)))⁻¹`, not a different orthogonalization. -/
noncomputable section
open scoped ComplexOrder MatrixOrder InnerProductSpace Topology BigOperators Matrix Matrix.Norms.L2Operator
namespace Cloning.PBWSymmetricFrame
open ContinuousLinearMap InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def symmetricFrame (v : ι→H) (i : ι) : H :=
  ∑ j,((CFC.sqrt (Matrix.gram ℂ v))⁻¹) j i • v j

theorem toEuclideanCLM_gram (v : ι→H) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (Matrix.gram ℂ v)=
      gram (synthesis (EuclideanSpace.basisFun ι ℂ) v) := by
  apply ContinuousLinearMap.ext
  intro x
  have hj (j : ι) : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (Matrix.gram ℂ v)
      (EuclideanSpace.basisFun ι ℂ j)=gram (synthesis (EuclideanSpace.basisFun ι ℂ) v)
      (EuclideanSpace.basisFun ι ℂ j) := by
    apply (EuclideanSpace.basisFun ι ℂ).repr.injective
    ext i
    rw [OrthonormalBasis.repr_apply_apply,OrthonormalBasis.repr_apply_apply,gram_entry]
    rw [EuclideanSpace.basisFun_inner,EuclideanSpace.basisFun_apply]
    change (Matrix.gram ℂ v *ᵥ (Pi.single j 1)) i=_
    simp
  rw [←(EuclideanSpace.basisFun ι ℂ).sum_repr' x]
  simp only [map_sum,map_smul,hj]

theorem toEuclideanCLM_sqrt_gram (v : ι→H) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (CFC.sqrt (Matrix.gram ℂ v))=
      CFC.sqrt (gram (synthesis (EuclideanSpace.basisFun ι ℂ) v)) := by
  rw [CFC.sqrt_eq_cfc,CFC.sqrt_eq_cfc,←toEuclideanCLM_gram v]
  exact StarAlgHomClass.map_cfc (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) NNReal.sqrt (Matrix.gram ℂ v)
    (hφ := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous)
    (ha := (Matrix.posSemidef_gram ℂ v).nonneg)
    (hφa := by rw [toEuclideanCLM_gram]; exact gram_nonneg _)

private theorem map_inverse_of_isUnit {A B : Type*} [Ring A] [Ring B]
    (e : A ≃+* B) (a : A) (ha : IsUnit a) :
    e (Ring.inverse a)=Ring.inverse (e a) := by
  have he : IsUnit (e a) := ha.map e
  calc
    e (Ring.inverse a)=e (Ring.inverse a)*(e a*Ring.inverse (e a)) := by
      rw [Ring.mul_inverse_cancel _ he,mul_one]
    _ = e (Ring.inverse a*a)*Ring.inverse (e a) := by rw [map_mul,mul_assoc]
    _ = Ring.inverse (e a) := by rw [Ring.inverse_mul_cancel _ ha,map_one,one_mul]

theorem symmetricFrame_eq_frame (v : ι→H)
    (hV : IsUnit (gram (synthesis (EuclideanSpace.basisFun ι ℂ) v))) :
    symmetricFrame v=frame (EuclideanSpace.basisFun ι ℂ) v := by
  let e := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
  have hg : IsUnit (Matrix.gram ℂ v) := by
    have h := hV.map e.symm
    rw [←toEuclideanCLM_gram v] at h
    simpa only [e,StarAlgEquiv.symm_apply_apply] using h
  have hs : IsUnit (CFC.sqrt (Matrix.gram ℂ v)) :=
    (CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_gram ℂ v).nonneg).mpr hg
  have hi : e ((CFC.sqrt (Matrix.gram ℂ v))⁻¹)=
      Ring.inverse (CFC.sqrt (gram (synthesis (EuclideanSpace.basisFun ι ℂ) v))) := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    have h := map_inverse_of_isUnit e.toRingEquiv _ hs
    exact h.trans (congrArg Ring.inverse (toEuclideanCLM_sqrt_gram v))
  funext i
  rw [frame,polar,ContinuousLinearMap.comp_apply,←hi,synthesis_apply]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [EuclideanSpace.basisFun_inner,EuclideanSpace.basisFun_apply]
  change _=(((CFC.sqrt (Matrix.gram ℂ v))⁻¹)*ᵥ (Pi.single i 1)) j
  simp

/-- Literal inverse-square-root orthonormalization, under an explicit small
Gram error, with the same order of quantitative error. -/
theorem symmetricFrame_properties (v : ι→H) (ε : ℝ)
    (herr : ∀ i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤ε)
    (hε : (Fintype.card ι : ℝ)^2*ε<1) :
    Orthonormal ℂ (symmetricFrame v) ∧
      Submodule.span ℂ (Set.range (symmetricFrame v))=Submodule.span ℂ (Set.range v) ∧
      ∀ i,‖symmetricFrame v i-v i‖≤(Fintype.card ι : ℝ)^2*ε := by
  have hV := gram_isUnit_of_error (EuclideanSpace.basisFun ι ℂ) v ε herr hε
  rw [symmetricFrame_eq_frame v hV]
  exact ⟨frame_orthonormal _ _ hV,span_frame _ _ hV,frame_error_le _ _ hV ε herr⟩

end Cloning.PBWSymmetricFrame
