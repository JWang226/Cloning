import Cloning.WeylSqueezerProductDisplacement

/-! Exact occupation slices for both partial traces of a physical appended
Fock register, with completeness and local displacement covariance. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
namespace Cloning.WeylSqueezerProduct
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {a b : ℕ}

def jointSignalSliceVector (m : Occupation b) (x : JointFock a b) : Fock a := by
  refine ⟨fun k => x (k,m),memℓp_gen ?_⟩
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective
    (fun i j h => congrArg Prod.fst h)

def jointIdlerSliceVector (m : Occupation a) (x : JointFock a b) : Fock b := by
  refine ⟨fun k => x (m,k),memℓp_gen ?_⟩
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective
    (fun i j h => congrArg Prod.snd h)

theorem jointSignalSliceVector_norm_le (m : Occupation b) (x : JointFock a b) :
    ‖jointSignalSliceVector m x‖≤‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num) x]
  exact Summable.tsum_le_tsum_of_inj (fun k : Occupation a => (k,m))
    (fun i j h => congrArg Prod.fst h)
    (fun p _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ => le_rfl)
    ((lp.memℓp (jointSignalSliceVector m x)).summable (by norm_num))
    ((lp.memℓp x).summable (by norm_num))

theorem jointIdlerSliceVector_norm_le (m : Occupation a) (x : JointFock a b) :
    ‖jointIdlerSliceVector m x‖≤‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num) x]
  exact Summable.tsum_le_tsum_of_inj (fun k : Occupation b => (m,k))
    (fun i j h => congrArg Prod.snd h)
    (fun p _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ => le_rfl)
    ((lp.memℓp (jointIdlerSliceVector m x)).summable (by norm_num))
    ((lp.memℓp x).summable (by norm_num))

def jointSignalSlice (m : Occupation b) : JointFock a b →L[ℂ] Fock a :=
  LinearMap.mkContinuous
    { toFun := jointSignalSliceVector m
      map_add' := by intro x y; ext k; rfl
      map_smul' := by intro c x; ext k; rfl }
    1 (fun x => by simpa only [one_mul] using jointSignalSliceVector_norm_le m x)

def jointIdlerSlice (m : Occupation a) : JointFock a b →L[ℂ] Fock b :=
  LinearMap.mkContinuous
    { toFun := jointIdlerSliceVector m
      map_add' := by intro x y; ext k; rfl
      map_smul' := by intro c x; ext k; rfl }
    1 (fun x => by simpa only [one_mul] using jointIdlerSliceVector_norm_le m x)

@[simp] theorem jointSignalSlice_apply (m : Occupation b) (x : JointFock a b) (k : Occupation a) :
    jointSignalSlice m x k=x (k,m) := rfl
@[simp] theorem jointIdlerSlice_apply (m : Occupation a) (x : JointFock a b) (k : Occupation b) :
    jointIdlerSlice m x k=x (m,k) := rfl

theorem jointSignalSlice_norm_sq_hasSum (x : JointFock a b) :
    HasSum (fun m => ‖jointSignalSlice m x‖^2) (‖x‖^2) := by
  have hf : HasSum (fun p : Occupation a × Occupation b => ‖x p‖^(2:ℕ)) (‖x‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0<(2:ENNReal).toReal) x
  have hs : HasSum (fun p : Occupation b × Occupation a => ‖x (p.2,p.1)‖^(2:ℕ)) (‖x‖^2) :=
    (Equiv.prodComm (Occupation b) (Occupation a)).hasSum_iff.mpr hf
  apply hs.prod_fiberwise
  intro m
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,jointSignalSlice_apply] using
    lp.hasSum_norm (by norm_num : 0<(2:ENNReal).toReal) (jointSignalSlice m x)

theorem jointIdlerSlice_norm_sq_hasSum (x : JointFock a b) :
    HasSum (fun m => ‖jointIdlerSlice m x‖^2) (‖x‖^2) := by
  have hf : HasSum (fun p : Occupation a × Occupation b => ‖x p‖^(2:ℕ)) (‖x‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0<(2:ENNReal).toReal) x
  apply hf.prod_fiberwise
  intro m
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,jointIdlerSlice_apply] using
    lp.hasSum_norm (by norm_num : 0<(2:ENNReal).toReal) (jointIdlerSlice m x)

theorem jointSignalSlice_inner_hasSum (x y : JointFock a b) :
    HasSum (fun m => ⟪jointSignalSlice m x,jointSignalSlice m y⟫_ℂ) ⟪x,y⟫_ℂ := by
  have hs : HasSum (fun p : Occupation b × Occupation a => ⟪x (p.2,p.1),y (p.2,p.1)⟫_ℂ) ⟪x,y⟫_ℂ :=
    (Equiv.prodComm (Occupation b) (Occupation a)).hasSum_iff.mpr (lp.hasSum_inner (𝕜 := ℂ) x y)
  exact hs.prod_fiberwise (fun m => lp.hasSum_inner (𝕜 := ℂ) (jointSignalSlice m x) (jointSignalSlice m y))

theorem jointIdlerSlice_inner_hasSum (x y : JointFock a b) :
    HasSum (fun m => ⟪jointIdlerSlice m x,jointIdlerSlice m y⟫_ℂ) ⟪x,y⟫_ℂ :=
  (lp.hasSum_inner (𝕜 := ℂ) x y).prod_fiberwise
    (fun m => lp.hasSum_inner (𝕜 := ℂ) (jointIdlerSlice m x) (jointIdlerSlice m y))

def signalSlice (m : Occupation b) : Fock (a+b) →L[ℂ] Fock a :=
  (jointSignalSlice m).comp (jointReindex a b).symm.toLinearIsometry.toContinuousLinearMap

def idlerSlice (m : Occupation a) : Fock (a+b) →L[ℂ] Fock b :=
  (jointIdlerSlice m).comp (jointReindex a b).symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem signalSlice_apply (m : Occupation b) (x : Fock (a+b)) (k : Occupation a) :
    signalSlice m x k=x (Fin.append k m) := jointReindex_symm_apply x (k,m)
@[simp] theorem idlerSlice_apply (m : Occupation a) (x : Fock (a+b)) (k : Occupation b) :
    idlerSlice m x k=x (Fin.append m k) := jointReindex_symm_apply x (m,k)

theorem signalSlice_norm_sq_hasSum (x : Fock (a+b)) :
    HasSum (fun m => ‖signalSlice m x‖^2) (‖x‖^2) := by
  simpa only [signalSlice,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,LinearIsometryEquiv.norm_map] using
    jointSignalSlice_norm_sq_hasSum ((jointReindex a b).symm x)

theorem idlerSlice_norm_sq_hasSum (x : Fock (a+b)) :
    HasSum (fun m => ‖idlerSlice m x‖^2) (‖x‖^2) := by
  simpa only [idlerSlice,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,LinearIsometryEquiv.norm_map] using
    jointIdlerSlice_norm_sq_hasSum ((jointReindex a b).symm x)

theorem signalSlice_inner_hasSum (x y : Fock (a+b)) :
    HasSum (fun m => ⟪signalSlice m x,signalSlice m y⟫_ℂ) ⟪x,y⟫_ℂ := by
  simpa only [signalSlice,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,LinearIsometryEquiv.inner_map_map] using
    jointSignalSlice_inner_hasSum ((jointReindex a b).symm x) ((jointReindex a b).symm y)

theorem idlerSlice_inner_hasSum (x y : Fock (a+b)) :
    HasSum (fun m => ⟪idlerSlice m x,idlerSlice m y⟫_ℂ) ⟪x,y⟫_ℂ := by
  simpa only [idlerSlice,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,LinearIsometryEquiv.inner_map_map] using
    jointIdlerSlice_inner_hasSum ((jointReindex a b).symm x) ((jointReindex a b).symm y)

@[simp] theorem signalSlice_tensor (m : Occupation b) (x : Fock a) (y : Fock b) :
    signalSlice m (tensorVector x y)=y m • x := by
  ext k
  simp [mul_comm]

@[simp] theorem idlerSlice_tensor (m : Occupation a) (x : Fock a) (y : Fock b) :
    idlerSlice m (tensorVector x y)=x m • y := by
  ext k
  simp

theorem signalSlice_displacement (z : Fin a → ℂ) (m : Occupation b) (x : Fock (a+b)) :
    signalSlice m (displacement (Fin.append z 0) x)=displacement z (signalSlice m x) := by
  have he : (signalSlice m).comp (displacement (Fin.append z 0))=
      (displacement z).comp (signalSlice m) := by
    apply coherent_ext
    intro u
    let v : Fin a → ℂ := fun i => u (Fin.castAdd b i)
    let w : Fin b → ℂ := fun j => u (Fin.natAdd a j)
    have hu : u=Fin.append v w := Fin.append_castAdd_natAdd.symm
    rw [hu,←tensorVector_coherent]
    simp only [ContinuousLinearMap.comp_apply,displacement_append_tensor,displacement_zero,
      ContinuousLinearMap.id_apply,signalSlice_tensor,map_smul]
  exact congrArg (fun T : Fock (a+b) →L[ℂ] Fock a => T x) he

theorem idlerSlice_displacement (z : Fin b → ℂ) (m : Occupation a) (x : Fock (a+b)) :
    idlerSlice m (displacement (Fin.append 0 z) x)=displacement z (idlerSlice m x) := by
  have he : (idlerSlice m).comp (displacement (Fin.append 0 z))=
      (displacement z).comp (idlerSlice m) := by
    apply coherent_ext
    intro u
    let v : Fin a → ℂ := fun i => u (Fin.castAdd b i)
    let w : Fin b → ℂ := fun j => u (Fin.natAdd a j)
    have hu : u=Fin.append v w := Fin.append_castAdd_natAdd.symm
    rw [hu,←tensorVector_coherent]
    simp only [ContinuousLinearMap.comp_apply,displacement_append_tensor,displacement_zero,
      ContinuousLinearMap.id_apply,idlerSlice_tensor,map_smul]
  exact congrArg (fun T : Fock (a+b) →L[ℂ] Fock b => T x) he

end Cloning.WeylSqueezerProduct
