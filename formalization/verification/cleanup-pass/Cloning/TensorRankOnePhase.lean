import Cloning.TensorRankOneProduct

/-! Highest-phase choices cancel from all complex operator conjugations. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {n m d : ℕ}
local instance {N D : ℕ} : FiniteDimensional ℂ (TensorRegister N (Fin D)) :=
  (registerBasis (Fin N → Fin D)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem top_vectors_unit_smul (Ψ Ξ : TensorRegister n (Fin (d+1)))
    (hΨ : ‖Ψ‖=1) (hΞ : ‖Ξ‖=1)
    (htΨ : collectiveGenerator n 0 0 Ψ=(n:ℂ) • Ψ)
    (htΞ : collectiveGenerator n 0 0 Ξ=(n:ℂ) • Ξ) :
    ∃c : ℂ, ‖c‖=1 ∧ Ψ=c • Ξ := by
  let a := Ψ (fun _=>0)
  let b := Ξ (fun _=>0)
  have ha : Ψ=a • highestTensor n d := top_occupation_eq_smul_highest Ψ htΨ
  have hb : Ξ=b • highestTensor n d := top_occupation_eq_smul_highest Ξ htΞ
  have hbn : b≠0 := by
    intro h
    rw [h,zero_smul] at hb
    rw [hb,norm_zero] at hΞ
    exact zero_ne_one hΞ
  have he : Ψ=(a/b) • Ξ := by
    rw [hb,smul_smul,div_mul_cancel₀ _ hbn]
    exact ha
  refine ⟨a/b,?_,he⟩
  have hh := congrArg norm he
  rw [hΨ,norm_smul,hΞ,mul_one] at hh
  exact hh.symm

section Conjugation
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem conjugation_unit_phase (F G : H →L[ℂ] K) (c : ℂ) (hc : ‖c‖=1)
    (hFG : F=c • G) (A : TraceClass H) :
    conjugationLinearMap F A=conjugationLinearMap G A := by
  have hcc : star c*c=1 := by
    simpa only [hc,Complex.ofReal_one,one_pow] using Complex.conj_mul' c
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change F (A.1 (F.adjoint x))=G (A.1 (G.adjoint x))
  rw [hFG]
  simp only [map_smulₛₗ,ContinuousLinearMap.smul_apply,map_smul,smul_smul,starRingEnd_apply,RingHom.id_apply]
  rw [hcc,one_smul]
end Conjugation

theorem cyclic_word_isometries_conjugation_eq
    (Ω : TensorRegister m (Fin (d+1)))
    (Ψ Ξ : TensorRegister n (Fin (d+1)))
    (hΨ : ‖Ψ‖=1) (hΞ : ‖Ξ‖=1)
    (htΨ : collectiveGenerator n 0 0 Ψ=(n:ℂ) • Ψ)
    (htΞ : collectiveGenerator n 0 0 Ξ=(n:ℂ) • Ξ)
    (F G : cyclicSector Ω →ₗᵢ[ℂ] TensorRegister n (Fin (d+1)))
    (hF : ∀w,F ⟨loweringWord Ω w,loweringWord_mem_cyclicSector Ω w⟩=loweringWord Ψ w)
    (hG : ∀w,G ⟨loweringWord Ω w,loweringWord_mem_cyclicSector Ω w⟩=loweringWord Ξ w)
    (A : TraceClass (cyclicSector Ω)) :
    conjugationLinearMap F.toContinuousLinearMap A=conjugationLinearMap G.toContinuousLinearMap A := by
  obtain ⟨c,hc,he⟩ := top_vectors_unit_smul Ψ Ξ hΨ hΞ htΨ htΞ
  have hword (w : List (PositiveRoot (d+1))) :
      F ⟨loweringWord Ω w,loweringWord_mem_cyclicSector Ω w⟩=
        c • G ⟨loweringWord Ω w,loweringWord_mem_cyclicSector Ω w⟩ := by
    rw [hF,hG,he,loweringWord_smul_highest]
  have hall (x : TensorRegister m (Fin (d+1))) (hx : x ∈ cyclicSector Ω) :
      F ⟨x,hx⟩=c • G ⟨x,hx⟩ := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w,rfl⟩ := hx; exact hword w
    | zero => change F 0=c • G 0; simp
    | add x y hx hy ihx ihy =>
        change F (⟨x,hx⟩+⟨y,hy⟩)=c • G (⟨x,hx⟩+⟨y,hy⟩)
        rw [map_add,map_add,smul_add,ihx,ihy]
    | smul a x hx ih =>
        change F (a • ⟨x,hx⟩)=c • G (a • ⟨x,hx⟩)
        rw [map_smul,map_smul,ih,smul_comm]
  apply conjugation_unit_phase F.toContinuousLinearMap G.toContinuousLinearMap c hc ?_ A
  apply ContinuousLinearMap.ext
  intro x
  exact hall x.val x.property

end Cloning.TensorLie
