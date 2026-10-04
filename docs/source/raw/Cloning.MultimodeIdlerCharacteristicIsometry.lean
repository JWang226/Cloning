import Cloning.MultimodeIdlerCharacteristicKernel
import Cloning.MultimodeIdlerCharacteristicPhase
import Cloning.WeylSqueezerProductDisplacement

/-! Exact Weyl intertwining of the actual negative-binomial isometry, proved
from its coherent kernel. No squeezer identification is assumed. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.MultimodeIdler
open Cloning.MultimodeCoherent Cloning.WeylSqueezerProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- The original occupation isometry in the appended mode register. -/
def appendedIsometry (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Fock d →ₗᵢ[ℂ] Cloning.MultimodeCoherent.Fock (d+d) :=
  (jointReindex d d).toLinearIsometry.comp (isometry q hq0 hq1)

def vacuumScale (q : Fin d → ℝ) (a : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (Real.sqrt (1-q i) : ℂ)*a i

def amplifierScale (q : Fin d → ℝ) (a : Fin d → ℂ) : Fin d → ℂ :=
  fun i => ((Real.sqrt (1-q i))⁻¹ : ℝ)*a i

def complementaryScale (q : Fin d → ℝ) (a : Fin d → ℂ) : Fin d → ℂ :=
  fun i => ((Real.sqrt (q i)*(Real.sqrt (1-q i))⁻¹ : ℝ):ℂ)*a i

lemma coherentKernel_eq_prod (q : Fin d → ℝ) (v w : Fin d → ℂ) :
    coherentKernel q v w = ∏ i, (Real.sqrt (1-q i):ℂ)*
      scalarCoherentKernel (Real.sqrt (q i)) (v i) (w i) := by
  simp only [coherentKernel, coherentVector, inner_tensorVector,
    ← scalarCoherentKernel_eq_inner, Finset.prod_mul_distrib]

lemma coherentKernel_shift (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (a v w : Fin d → ℂ) :
    displacementPhase (-(amplifierScale q a)) v *
      displacementPhase (-(complementaryScale q (star a))) w *
      coherentKernel q (v-amplifierScale q a) (w-complementaryScale q (star a)) =
      coherentKernel q v w * displacementPhase (-a) (vacuumScale q v) := by
  simp only [displacementPhase, coherentKernel_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hrel : (1-(Real.sqrt (q i))^2)*(Real.sqrt (1-q i))⁻¹=Real.sqrt (1-q i) := by
    rw [Real.sq_sqrt (hq0 i), ← Real.sq_sqrt (sub_nonneg.mpr (hq1 i).le)]
    have hs : Real.sqrt (1-q i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (hq1 i)))
    simp [pow_two, hs]
  have hh := scalarCoherentKernel_shift (Real.sqrt (1-q i)) (Real.sqrt (q i))
    (Real.sqrt (1-q i))⁻¹ hrel (a i) (v i) (w i)
  dsimp only [amplifierScale, complementaryScale, vacuumScale, Pi.neg_apply,
    Pi.sub_apply, Pi.star_apply]
  calc
    _ = (Real.sqrt (1-q i):ℂ) *
      (Cloning.ComplexCoherent.displacementPhase (-(((Real.sqrt (1-q i))⁻¹:ℝ):ℂ)*a i) (v i) *
      Cloning.ComplexCoherent.displacementPhase
        (-((Real.sqrt (q i)*(Real.sqrt (1-q i))⁻¹:ℝ):ℂ)*star (a i)) (w i) *
      scalarCoherentKernel (Real.sqrt (q i))
        (v i-(((Real.sqrt (1-q i))⁻¹:ℝ):ℂ)*a i)
        (w i-((Real.sqrt (q i)*(Real.sqrt (1-q i))⁻¹:ℝ):ℂ)*star (a i))) := by
          simp only [neg_mul]
          ring
    _ = _ := by
      simp only [neg_mul] at hh ⊢
      rw [hh]
      ring

lemma vacuumScale_shift (q : Fin d → ℝ) (hq1 : ∀ i, q i < 1) (a v : Fin d → ℂ) :
    vacuumScale q (v-amplifierScale q a) = -a+vacuumScale q v := by
  ext i
  have hs : Real.sqrt (1-q i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (hq1 i)))
  simp only [vacuumScale, amplifierScale, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
    Complex.ofReal_inv, mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs)]
  ring

lemma appendedIsometry_adjoint_coherent (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (v w : Fin d → ℂ) :
    (appendedIsometry q hq0 hq1).toContinuousLinearMap.adjoint
      (coherentVector (Fin.append v w)) = coherentKernel q v w • coherentVector (vacuumScale q v) := by
  change (((jointReindex d d) : Cloning.WeylSqueezerProduct.JointFock d d →L[ℂ]
      Cloning.MultimodeCoherent.Fock (d+d)).comp
    (isometry q hq0 hq1).toContinuousLinearMap).adjoint _ = _
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    ContinuousLinearMap.comp_apply, ← tensorVector_coherent]
  change (isometry q hq0 hq1).toContinuousLinearMap.adjoint
    ((jointReindex d d).symm (jointReindex d d (jointTensor (coherentVector v) (coherentVector w)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, isometry_adjoint_jointTensor_coherent]
  rfl

lemma appendedIsometry_adjoint_intertwines (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) :
    (appendedIsometry q hq0 hq1).toContinuousLinearMap.adjoint.comp
      (displacement (-Fin.append (amplifierScale q a) (complementaryScale q (star a)))) =
    (displacement (-a)).comp (appendedIsometry q hq0 hq1).toContinuousLinearMap.adjoint := by
  apply coherent_ext
  intro z
  let v : Fin d → ℂ := fun i => z (Fin.castAdd d i)
  let w : Fin d → ℂ := fun i => z (Fin.natAdd d i)
  have hz : Fin.append v w = z := Fin.append_castAdd_natAdd
  rw [← hz]
  have hneg : -Fin.append (amplifierScale q a) (complementaryScale q (star a)) =
      Fin.append (-(amplifierScale q a)) (-(complementaryScale q (star a))) := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Pi.neg_apply, Fin.append_left, Fin.append_right]
  have hadd : Fin.append (-(amplifierScale q a)) (-(complementaryScale q (star a)))+
      Fin.append v w = Fin.append (v-amplifierScale q a) (w-complementaryScale q (star a)) := by
    rw [append_add]
    congr 1 <;> abel
  simp only [ContinuousLinearMap.comp_apply, displacement_coherentVector, map_smul,
    hneg, hadd, appendedIsometry_adjoint_coherent, displacementPhase_append,
    smul_smul, coherentKernel_shift q hq0 hq1, vacuumScale_shift q hq1]

/-- The literal isometry intertwines input Weyl displacements with the two
output Weyl displacements, including the positive conjugated complementary shift. -/
theorem appendedIsometry_intertwines (q : Fin d → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (a : Fin d → ℂ) :
    (appendedIsometry q hq0 hq1).toContinuousLinearMap.comp (displacement a) =
      (displacement (Fin.append (amplifierScale q a) (complementaryScale q (star a)))).comp
        (appendedIsometry q hq0 hq1).toContinuousLinearMap := by
  have hh := congrArg (fun T => ContinuousLinearMap.adjoint T)
    (appendedIsometry_adjoint_intertwines q hq0 hq1 a)
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    displacement_adjoint, neg_neg] using hh.symm

end Cloning.MultimodeIdler
