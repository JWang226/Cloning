import Cloning.PBWSymmetricFrameRateMatrix
import Cloning.TensorGibbsHeight
import Cloning.TensorPBWFiniteSector

/-! Exact physical Cartan weight spaces are spanned by the matching canonical
PBW occupations. This identifies the symmetric block frame with the actual
weight space, rather than only with an abstract coordinate span. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PBWSymmetricFrame
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem span_inter_of_orthogonal (v : ι→H) (W : Submodule ℂ H) (P : ι→Prop)
    [DecidablePred P] (hkeep : ∀i,P i→v i∈W)
    (hdrop : ∀i,¬P i→∀x∈W,⟪v i,x⟫_ℂ=0) :
    Submodule.span ℂ (Set.range v) ⊓ W=
      Submodule.span ℂ (Set.range (fun i : {i // P i}=>v i.val)) := by
  let S := Submodule.span ℂ (Set.range (fun i : {i // P i}=>v i.val))
  have hS : S≤W := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hkeep i.val i.property)
  have hSV : S≤Submodule.span ℂ (Set.range v) :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact Submodule.subset_span ⟨i.val,rfl⟩)
  apply le_antisymm
  · intro x hx
    let y := S.starProjection x
    let z := x-y
    have hy : y∈S := (S.orthogonalProjection x).property
    have hzW : z∈W := W.sub_mem hx.2 (hS hy)
    have hzV : z∈Submodule.span ℂ (Set.range v) :=
      Submodule.sub_mem _ hx.1 (hSV hy)
    have hzS : z∈Sᗮ := S.sub_starProjection_mem_orthogonal x
    have hi (i : ι) : ⟪v i,z⟫_ℂ=0 := by
      by_cases h : P i
      · exact (S.mem_orthogonal z).mp hzS (v i) (Submodule.subset_span ⟨⟨i,h⟩,rfl⟩)
      · exact hdrop i h z hzW
    have hall : ∀a∈Submodule.span ℂ (Set.range v),⟪a,z⟫_ℂ=0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha => rcases ha with ⟨i,rfl⟩; exact hi i
      | zero => simp
      | add a b ha hb h1 h2 => simp [inner_add_left,h1,h2]
      | smul c a ha h => simp [inner_smul_left,h]
    have hz : z=0 := inner_self_eq_zero.mp (hall z hzV)
    have he : x=y := sub_eq_zero.mp hz
    exact he ▸ hy
  · exact le_inf hSV hS

end Cloning.PBWSymmetricFrame

namespace Cloning.TensorLie
open PBWSymmetricFrame Cloning.PCT
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n→Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def cartanWeightSpace (n : ℕ) (mu : Fin d→ℕ) (η : Fin d→ℤ) :
    Submodule ℂ (TensorRegister n (Fin d)) :=
  ⨅ a : Fin d,LinearMap.ker ((collectiveGenerator n a a).toLinearMap-
    ((mu a:ℂ)+(η a:ℂ)) • LinearMap.id)

theorem mem_cartanWeightSpace (mu : Fin d→ℕ) (η : Fin d→ℤ)
    (x : TensorRegister n (Fin d)) : x∈cartanWeightSpace n mu η ↔
      ∀a,collectiveGenerator n a a x=((mu a:ℂ)+(η a:ℂ)) • x := by
  simp only [cartanWeightSpace,Submodule.mem_iInf,LinearMap.mem_ker,
    LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,sub_eq_zero,
    ContinuousLinearMap.coe_coe]

def WeightOccupation (d R : ℕ) (η : Fin d→ℤ) :=
  {k : HeightOccupation d R // loweringWeight (canonicalWord k.val)=η}

instance (d R : ℕ) (η : Fin d→ℤ) : Fintype (WeightOccupation d R η) :=
  inferInstanceAs (Fintype {k : HeightOccupation d R // loweringWeight (canonicalWord k.val)=η})

theorem canonicalWeight_span (Ω : TensorRegister n (Fin d)) (mu : Fin d→ℕ)
    (hweight : ∀a,collectiveGenerator n a a Ω=(mu a:ℂ) • Ω)
    (R : ℕ) (η : Fin d→ℤ) :
    cyclicCutoff Ω (R:ℤ) ⊓ cartanWeightSpace n mu η=
      Submodule.span ℂ (Set.range (fun k : WeightOccupation d R η=>
        loweringWord Ω (canonicalWord k.val.val))) := by
  classical
  rw [cyclicCutoff_eq_span_canonical]
  apply span_inter_of_orthogonal
  · intro k hk
    apply (mem_cartanWeightSpace mu η _).mpr
    intro a
    rw [cartan_loweringWord Ω (fun a=>(mu a:ℂ)) hweight, hk]
  · intro k hk x hx
    obtain ⟨a,ha⟩ := Function.ne_iff.mp hk
    apply inner_eq_zero_of_real_eigenvalues (collectiveGenerator n a a).toLinearMap
      (cartan_isSymmetric a) _ _ ((mu a:ℝ)+loweringWeight (canonicalWord k.val) a)
        ((mu a:ℝ)+η a)
    · simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_intCast] using
        cartan_loweringWord Ω (fun a=>(mu a:ℂ)) hweight (canonicalWord k.val) a
    · simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_intCast] using
        (mem_cartanWeightSpace mu η x).mp hx a
    · intro he
      exact ha (by exact_mod_cast add_left_cancel he)

/-- If the weight has height at most `R`, its full physical eigenspace in the
cyclic sector is already the finite-height block. -/
theorem cyclicWeight_eq_cutoffWeight (Ω : TensorRegister n (Fin d)) (mu : Fin d→ℕ)
    (hweight : ∀a,collectiveGenerator n a a Ω=(mu a:ℂ) • Ω)
    (R : ℕ) (η : Fin d→ℤ) (hη : ∑a,(a.val:ℤ)*η a≤(R:ℤ)) :
    cyclicSector Ω ⊓ cartanWeightSpace n mu η=
      cyclicCutoff Ω (R:ℤ) ⊓ cartanWeightSpace n mu η := by
  apply le_antisymm
  · rw [cyclicSector_eq_tensorSize_cutoff Ω mu hweight,
      canonicalWeight_span Ω mu hweight (n*d) η]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    constructor
    · apply loweringWord_mem_cyclicCutoff
      rw [←loweringWeight_index_sum,k.property]
      exact hη
    · apply (mem_cartanWeightSpace mu η _).mpr
      intro a
      rw [cartan_loweringWord Ω (fun a=>(mu a:ℂ)) hweight,k.property]
  · exact inf_le_inf (cyclicCutoff_le_cyclicSector Ω _) le_rfl

end Cloning.TensorLie
