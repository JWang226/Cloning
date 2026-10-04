import Cloning.PCTRankPurificationGeneralPhysical
import Cloning.TensorHighestGramIsometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Equal reduced density matrices give an actual unitary change of the
finite environment, including singular purifications. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.PCTPurificationChannel Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]
local instance generalPurificationFiniteDimensional : FiniteDimensional ℂ (Register E) :=
  (registerBasis E).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def rowCombination (ψ : Register (A×E)) : (A→ℂ)→ₗ[ℂ] Register E where
  toFun x := ∑ a,x a • environmentRow ψ a
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum,smul_smul]

theorem environmentRow_inner (ψ : Register (A×E)) (a b : A) :
    ⟪environmentRow ψ a,environmentRow ψ b⟫_ℂ=reducedDensityMatrix ψ b a := by
  simp only [lp.inner_eq_tsum,tsum_fintype,RCLike.inner_apply,environmentRow_apply,
    reducedDensityMatrix,starRingEnd_apply,mul_comm]

theorem rowCombination_norm_eq (ψ φ : Register (A×E))
    (h : reducedDensityMatrix ψ=reducedDensityMatrix φ) (x : A→ℂ) :
    ‖rowCombination ψ x‖=‖rowCombination φ x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜:=ℂ),norm_eq_sqrt_re_inner (𝕜:=ℂ)]
  congr 2
  simp only [rowCombination,LinearMap.coe_mk,AddHom.coe_mk,
    inner_sum, sum_inner,inner_smul_left,inner_smul_right,environmentRow_inner,h]

/-- The actual finite environment transformation is constructed by extending
the isometry between the spans of the purification rows. -/
theorem exists_environment_isometry_of_reduced_eq (ψ φ : Register (A×E))
    (h : reducedDensityMatrix ψ=reducedDensityMatrix φ) :
    ∃W : Register E→ₗᵢ[ℂ] Register E, environmentRotate W ψ=φ := by
  let f := rowCombination ψ
  let g := rowCombination φ
  let e := sameNormRangeIsometry f g (rowCombination_norm_eq ψ φ h)
  let L : LinearMap.range f→ₗᵢ[ℂ] Register E := (LinearMap.range g).subtypeₗᵢ.comp e.toLinearIsometry
  refine ⟨L.extend,?_⟩
  have he (x : A→ℂ) : L.extend (f x)=g x := by
    have ht := LinearIsometry.extend_apply L ⟨f x,LinearMap.mem_range_self f x⟩
    rw [ht]
    exact sameNormRangeIsometry_apply f g (rowCombination_norm_eq ψ φ h) x _
  have hrow (a : A) : L.extend (environmentRow ψ a)=environmentRow φ a := by
    have hh := he (Pi.single a 1)
    simpa only [f,g,rowCombination,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply,
      ite_smul,zero_smul,one_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh
  ext ⟨a,b⟩
  simp only [environmentRotate_apply,hrow,environmentRow_apply]

variable [Nonempty E]

/-- Every finite environment isometry is the physical matrix action of a
unitary, with the transpose convention used by Haar purification. -/
theorem exists_purificationEnvironment (W : Register E→ₗᵢ[ℂ] Register E) :
    ∃U : unitary (Matrix E E ℂ),purificationEnvironment U=W := by
  let Q : Matrix E E ℂ := fun a b=>W (lp.single 2 b 1) a
  have hQ : Qᴴ*Q=1 := by
    ext a b
    have h := W.inner_map_map (lp.single 2 a 1) (lp.single 2 b 1)
    have hbase : ⟪(lp.single 2 a 1 : Register E),lp.single 2 b 1⟫_ℂ=
        if a=b then 1 else 0 := by
      simp [register_inner_single,lp.single_apply,Pi.single_apply,eq_comm]
    rw [hbase] at h
    simpa only [lp.inner_eq_tsum,tsum_fintype,RCLike.inner_apply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,starRingEnd_apply,
      Q,mul_comm] using h
  let V : unitary (Matrix E E ℂ) := ⟨Q,Matrix.mem_unitaryGroup_iff'.mpr hQ⟩
  refine ⟨Matrix.UnitaryGroup.transpose V,?_⟩
  ext x a
  have hx : x=∑b,x b • (lp.single 2 b 1 : Register E) := by
    ext b
    simp [lp.single_apply,Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [purificationEnvironment,unitaryRegister_apply,Matrix.UnitaryGroup.transpose,
    Matrix.transpose_apply,V,Q,map_sum,map_smul,lp.coeFn_sum,Finset.sum_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

/-- Any two purifications in the same environment differ by an actual
unitary, without a full-rank hypothesis. -/
theorem exists_environment_unitary_of_reduced_eq (ψ φ : Register (A×E))
    (h : reducedDensityMatrix ψ=reducedDensityMatrix φ) :
    ∃U : unitary (Matrix E E ℂ),environmentRotate (purificationEnvironment U) ψ=φ := by
  obtain ⟨W,hW⟩ := exists_environment_isometry_of_reduced_eq ψ φ h
  obtain ⟨U,hU⟩ := exists_purificationEnvironment W
  exact ⟨U,hU.symm ▸ hW⟩

end Cloning.PCTRankPurification
