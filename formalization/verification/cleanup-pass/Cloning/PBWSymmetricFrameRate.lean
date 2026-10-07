import Cloning.PBWSymmetricFrameRateCFC

/-! Literal symmetric normalization of a finite Hilbert-space family, with a
quantitative Gram-error bound and exact preservation of its span. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PBWSymmetricFrame
open ContinuousLinearMap InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {ι E H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def synthesis (b : OrthonormalBasis ι ℂ E) (v : ι→H) : E →L[ℂ] H :=
  ∑ i, rankOne ℂ (v i) (b i)

theorem synthesis_apply (b : OrthonormalBasis ι ℂ E) (v : ι→H) (x : E) :
    synthesis b v x=∑ i,⟪b i,x⟫_ℂ • v i := by
  simp only [synthesis,ContinuousLinearMap.sum_apply,rankOne_apply]

@[simp] theorem synthesis_basis (b : OrthonormalBasis ι ℂ E) (v : ι→H) (i : ι) :
    synthesis b v (b i)=v i := by
  rw [synthesis_apply]
  simp only [orthonormal_iff_ite.mp b.orthonormal,ite_smul,one_smul,zero_smul]
  simp

theorem gram_entry (b : OrthonormalBasis ι ℂ E) (v : ι→H) (i j : ι) :
    ⟪b i,gram (synthesis b v) (b j)⟫_ℂ=⟪v i,v j⟫_ℂ := by
  rw [gram,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    synthesis_basis,synthesis_basis]

theorem operator_eq_sum_rankOne (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) :
    T=∑ i,∑ j,⟪b i,T (b j)⟫_ℂ • rankOne ℂ (b i) (b j) := by
  ext x
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    rankOne_apply,smul_smul]
  rw [Finset.sum_comm]
  calc
    T x=∑ j,⟪b j,x⟫_ℂ • T (b j) := by
      conv_lhs => rw [←b.sum_repr' x]
      simp only [map_sum,map_smul]
    _ = ∑ j,∑ i,(⟪b i,T (b j)⟫_ℂ*⟪b j,x⟫_ℂ) • b i := by
      apply Finset.sum_congr rfl
      intro j _
      conv_lhs => rw [←b.sum_repr' (T (b j))]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,mul_comm]

theorem operator_norm_le_entries (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) :
    ‖T‖≤∑ i,∑ j,‖⟪b i,T (b j)⟫_ℂ‖ := by
  conv_lhs => rw [operator_eq_sum_rankOne b T]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_smul,norm_rankOne,b.orthonormal.norm_eq_one,mul_one,le_refl]

theorem gram_error_norm_le (b : OrthonormalBasis ι ℂ E) (v : ι→H) (ε : ℝ)
    (herr : ∀ i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤ε) :
    ‖gram (synthesis b v)-1‖≤(Fintype.card ι : ℝ)^2*ε := by
  apply (operator_norm_le_entries b _).trans
  calc
    (∑i,∑j,‖⟪b i,(gram (synthesis b v)-1) (b j)⟫_ℂ‖)≤∑i : ι,∑j : ι,ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [ContinuousLinearMap.sub_apply,one_apply,inner_sub_right,
        gram_entry,orthonormal_iff_ite.mp b.orthonormal] using herr i j
    _ = _ := by simp [pow_two,mul_assoc]

theorem gram_isUnit_of_error (b : OrthonormalBasis ι ℂ E) (v : ι→H) (ε : ℝ)
    (herr : ∀ i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤ε)
    (hε : (Fintype.card ι : ℝ)^2*ε<1) : IsUnit (gram (synthesis b v)) := by
  have h : ‖1-gram (synthesis b v)‖<1 := by
    rw [norm_sub_rev]
    exact (gram_error_norm_le b v ε herr).trans_lt hε
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h

def frame (b : OrthonormalBasis ι ℂ E) (v : ι→H) (i : ι) : H :=
  polar (synthesis b v) (b i)

theorem frame_orthonormal (b : OrthonormalBasis ι ℂ E) (v : ι→H)
    (hV : IsUnit (gram (synthesis b v))) : Orthonormal ℂ (frame b v) := by
  let T : E →ₗᵢ[ℂ] H := ⟨(polar (synthesis b v)).toLinearMap,polar_norm _ hV⟩
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪T (b i),T (b j)⟫_ℂ=_
  rw [T.inner_map_map,orthonormal_iff_ite.mp b.orthonormal]

theorem frame_error_le (b : OrthonormalBasis ι ℂ E) (v : ι→H)
    (hV : IsUnit (gram (synthesis b v))) (ε : ℝ)
    (herr : ∀ i j,‖⟪v i,v j⟫_ℂ-(if i=j then 1 else 0 : ℂ)‖≤ε) (i : ι) :
    ‖frame b v i-v i‖≤(Fintype.card ι : ℝ)^2*ε := by
  have h := polar_sub_apply_le (synthesis b v) hV (b i)
  simp only [synthesis_basis,b.orthonormal.norm_eq_one,mul_one] at h
  exact h.trans (gram_error_norm_le b v ε herr)

theorem frame_mem_span (b : OrthonormalBasis ι ℂ E) (v : ι→H) (i : ι) :
    frame b v i∈Submodule.span ℂ (Set.range v) := by
  unfold frame polar
  rw [ContinuousLinearMap.comp_apply,synthesis_apply]
  exact Submodule.sum_mem _ (fun j _=>Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j)))

theorem span_frame (b : OrthonormalBasis ι ℂ E) (v : ι→H)
    (hV : IsUnit (gram (synthesis b v))) :
    Submodule.span ℂ (Set.range (frame b v))=Submodule.span ℂ (Set.range v) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact frame_mem_span b v i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have he : v i=polar (synthesis b v) (CFC.sqrt (gram (synthesis b v)) (b i)) := by
      simpa only [ContinuousLinearMap.comp_apply,synthesis_basis] using
        (congrArg (fun T : E →L[ℂ] H=>T (b i)) (polar_mul_sqrt (synthesis b v) hV)).symm
    rw [he,←b.sum_repr' (CFC.sqrt (gram (synthesis b v)) (b i)),map_sum]
    simp only [map_smul]
    exact Submodule.sum_mem _ (fun j _=>Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))

end Cloning.PBWSymmetricFrame
