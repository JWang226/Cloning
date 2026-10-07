import Cloning.TensorRankOneHighest
import Cloning.TensorFlatProjectorMixture

/-! The actual rank-one sector Gibbs density is the highest-vector projector. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Matrix
namespace Cloning.TensorLie
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.TensorLAN
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem top_occupation_eq_smul_basis (a : Fin d) (Ω : TensorRegister n (Fin d))
    (hΩ : collectiveGenerator n a a Ω=(n:ℂ) • Ω) :
    Ω=Ω (fun _=>a) • registerBasis (Fin n → Fin d) (fun _=>a) := by
  ext w
  have he := congrArg (fun x : TensorRegister n (Fin d) => x w) hΩ
  simp only [collectiveGenerator_diagonal,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] at he
  by_cases hw : w=(fun _=>a)
  · subst w
    simp [registerBasis_apply,lp.single_apply,Pi.single_apply]
  · have hne : occupancy w a ≠ n := by
      intro hn
      apply hw
      have hall : ∀ i : Fin n, w i=a := by
        simpa only [Finset.card_univ,Fintype.card_fin,Finset.mem_univ,true_implies,occupancy] using
          (Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin n)))
            (p := fun i=>w i=a)).mp (by simpa only [Finset.card_univ,Fintype.card_fin] using hn)
      exact funext hall
    have hn : (occupancy w a : ℂ) ≠ n := by exact_mod_cast hne
    have hz : Ω w=0 := (mul_eq_mul_right_iff.mp he).resolve_left hn
    simp [registerBasis_apply,lp.single_apply,Pi.single_apply,hw,hz]

theorem tensorOperator_coordinate_projection (a : Fin d) (x : TensorRegister n (Fin d)) :
    tensorOperator n (Matrix.diagonal (fun b => if b=a then (1:ℂ) else 0)) x =
      x (fun _=>a) • registerBasis (Fin n → Fin d) (fun _=>a) := by
  ext w
  rw [tensorOperator_diagonal_apply]
  by_cases hw : w=(fun _=>a)
  · subst w
    simp [registerBasis_apply,lp.single_apply,Pi.single_apply]
  · have ht : ∃ t, w t≠a := by
      by_contra hh
      push_neg at hh
      exact hw (funext hh)
    obtain ⟨t,ht⟩ := ht
    have hp : (∏ i : Fin n, if w i=a then (1:ℂ) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
    simp [hp,registerBasis_apply,lp.single_apply,Pi.single_apply,hw]

theorem tensorOperator_coordinate_projection_highest (a : Fin d)
    (Ω : TensorRegister n (Fin d)) (hΩnorm : ‖Ω‖=1)
    (hΩ : collectiveGenerator n a a Ω=(n:ℂ) • Ω) (x : TensorRegister n (Fin d)) :
    tensorOperator n (Matrix.diagonal (fun b => if b=a then (1:ℂ) else 0)) x =
      ⟪Ω,x⟫_ℂ • Ω := by
  let e := registerBasis (Fin n → Fin d) (fun _=>a)
  let c := Ω (fun _=>a)
  have he : Ω=c • e := top_occupation_eq_smul_basis a Ω hΩ
  have hc : star c*c=1 := by
    have hh : ⟪Ω,Ω⟫_ℂ=1 := by simp [inner_self_eq_norm_sq_to_K,hΩnorm]
    rw [he,inner_smul_left,inner_smul_right] at hh
    simpa only [e,inner_self_eq_norm_sq_to_K,
      (registerBasis (Fin n → Fin d)).orthonormal.1,one_pow,
      RCLike.ofReal_one,mul_one,RCLike.star_def] using hh
  rw [tensorOperator_coordinate_projection,he,inner_smul_left]
  have hi : ⟪e,x⟫_ℂ=x (fun _=>a) := by
    simpa only [e,registerBasis_apply] using register_inner_single (fun _ : Fin n=>a) x
  rw [hi,smul_smul]
  have hh : (star c*x (fun _=>a))*c=x (fun _=>a) := by
    calc _ = (star c*c)*x (fun _=>a) := by ring
         _ = _ := by rw [hc,one_mul]
  exact (congrArg (fun z : ℂ => z • e) hh).symm

/-- A coordinate-pure spectrum gives exactly the normalized highest projector. -/
theorem sectorGibbsDensity_coordinate (a : Fin d)
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ b,collectiveGenerator n b b Ω=(mu b:ℂ) • Ω)
    (hraise : ∀ b c,b<c→collectiveGenerator n b c Ω=0)
    (hΩnorm : ‖Ω‖=1) (ha : mu a=n) :
    sectorGibbsDensity Ω mu hweight hraise (fun b=>if b=a then 1 else 0)=
      vectorProjector (⟨Ω,highest_mem_cyclicSector Ω⟩ : cyclicSector Ω) := by
  let v : cyclicSector Ω := ⟨Ω,highest_mem_cyclicSector Ω⟩
  have hv : ‖v‖=1 := hΩnorm
  have hw : sectorGibbsWeight Ω mu hweight hraise (fun b=>if b=a then 1 else 0)=
      vectorProjector v := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change tensorOperator n (Matrix.diagonal (fun b=>((if b=a then 1 else 0 : ℝ):ℂ)))
      (x : TensorRegister n (Fin d)) = ⟪Ω,(x : TensorRegister n (Fin d))⟫_ℂ • Ω
    simp only [apply_ite,Complex.ofReal_one,Complex.ofReal_zero]
    exact tensorOperator_coordinate_projection_highest a Ω hΩnorm (ha ▸ hweight a) x
  have hZ : sectorPartitionFunction Ω mu hweight hraise (fun b=>if b=a then 1 else 0)=1 := by
    change ‖sectorGibbsWeight Ω mu hweight hraise _‖=1
    rw [hw,norm_vectorProjector,hv,one_pow]
  rw [sectorGibbsDensity,hZ,hw]
  simp only [inv_one,Complex.ofReal_one,one_smul]
  rfl

/-- This is the literal canonical sector state used by the global channel. -/
theorem canonicalGibbsDensity_rankOne {k : ℕ} (H : PhysicalHighestTensor n (1+k))
    (hH : H.weight 0=n) :
    canonicalGibbsDensity H (rankFlatSpectrum 1 k)=
      vectorProjector (⟨partitionHighestTensor H.weight H.weight_antitone,
        highest_mem_cyclicSector _⟩ : H.CanonicalSector) := by
  have hp : rankFlatSpectrum 1 k=(fun b : Fin (1+k)=>if b=0 then 1 else 0) := by
    funext b
    have hb : b.val<1 ↔ b=0 := by
      constructor
      · intro h; apply Fin.ext; change b.val=0; omega
      · rintro rfl; exact Nat.zero_lt_one
    simp only [rankFlatSpectrum,Nat.cast_one,div_one,hb]
  rw [hp]
  exact sectorGibbsDensity_coordinate 0 _ H.weight
    (partitionHighestTensor_cartan H.weight H.weight_antitone)
    (partitionHighestTensor_raising_zero H.weight H.weight_antitone)
    (partitionHighestTensor_norm H.weight H.weight_antitone) (hH.trans H.weight_sum.symm)

theorem canonicalRotatedGibbs_rankOne {k : ℕ} (H : PhysicalHighestTensor n (1+k))
    (hH : H.weight 0=n) (U : Matrix (Fin (1+k)) (Fin (1+k)) ℂ) :
    canonicalRotatedGibbs H U (rankFlatSpectrum 1 k)=
      vectorProjector (H.canonicalTensorOperator U
        ⟨partitionHighestTensor H.weight H.weight_antitone,highest_mem_cyclicSector _⟩) := by
  rw [canonicalRotatedGibbs,canonicalGibbsDensity_rankOne H hH]
  exact conjugationLinearMap_vectorProjector _ _

end Cloning.TensorLie
