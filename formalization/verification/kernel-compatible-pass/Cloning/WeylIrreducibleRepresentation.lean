import Cloning.WeylFockDecomposition
import Cloning.WeylGaussianTotality
import Cloning.IsometricRecovery

/-! Every regular Weyl representation with scalar commutant is genuinely
unitarily equivalent to the concrete multimode Fock representation. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder
namespace Cloning.WeylGNS
open Cloning.MultimodeCoherent Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

theorem RegularWeyl.operator_adjoint (a : Fin d → ℂ) :
    (W.operator a).adjoint=W.operator (-a) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact W.inner_operator a x y

/-- Every nonzero regular representation has an actual unit vacuum vector. -/
theorem RegularWeyl.exists_unit_vacuum [Nontrivial H] :
    ∃ x : W.vacuumSpace, ‖(x : H)‖=1 := by
  have hex : ∃ y : H, W.gaussianProjection y ≠ 0 := by
    by_contra hn
    have hz : ∀ y : H, W.gaussianProjection y=0 := by simpa using hn
    obtain ⟨v,hv⟩ := exists_ne (0:H)
    exact hv (W.eq_zero_of_projection_translates_zero v (fun a => hz _))
  obtain ⟨y,hy⟩ := hex
  let x : W.vacuumSpace := ⟨W.gaussianProjection y,⟨y,rfl⟩⟩
  have hx : ‖(x:H)‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  refine ⟨((‖(x:H)‖⁻¹ : ℝ) : ℂ) • x, ?_⟩
  change ‖((‖(x:H)‖⁻¹ : ℝ) : ℂ) • (x:H)‖=1
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hx]

/-- Scalar commutant makes the isometric vacuum copy surjective. -/
theorem RegularWeyl.vacuumEmbedding_surjective (x : W.vacuumSpace) (hx : ‖(x:H)‖=1)
    (hirr : ∀ T : H →L[ℂ] H,
      (∀ a, T.comp (W.operator a)=(W.operator a).comp T) →
        ∃ c : ℂ, T=c • ContinuousLinearMap.id ℂ H) :
    Function.Surjective (W.vacuumEmbedding x hx) := by
  let V := W.vacuumEmbedding x hx
  have hV (a : Fin d → ℂ) : (W.operator a).comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp (displacement a) := by
    ext v
    exact (W.vacuumEmbedding_intertwines x hx a v).symm
  have hVa (a : Fin d → ℂ) : V.toContinuousLinearMap.adjoint.comp (W.operator a) =
      (displacement a).comp V.toContinuousLinearMap.adjoint := by
    have he := congrArg ContinuousLinearMap.adjoint (hV (-a))
    simpa only [ContinuousLinearMap.adjoint_comp, W.operator_adjoint,
      displacement_adjoint, neg_neg] using he
  let Q := V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint
  have hQ (a : Fin d → ℂ) : Q.comp (W.operator a)=(W.operator a).comp Q := by
    change (V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint).comp (W.operator a)=_
    rw [ContinuousLinearMap.comp_assoc, hVa, ← ContinuousLinearMap.comp_assoc,
      ← hV a, ContinuousLinearMap.comp_assoc]
  obtain ⟨c,hc⟩ := hirr Q hQ
  have hQx : Q (x:H)=(x:H) := by
    have he : V (coherentVector 0)=(x:H) := by
      change W.vacuumEmbedding x hx (coherentVector 0)=(x:H)
      rw [W.vacuumEmbedding_coherent, W.operator_zero, ContinuousLinearMap.id_apply]
    rw [← he]
    exact congrArg V (isometry_adjoint_apply_self V (coherentVector 0))
  have hc1 : c=1 := by
    have hh := congrArg (fun T : H →L[ℂ] H => ⟪(x:H),T (x:H)⟫_ℂ) hc
    change ⟪(x:H),Q (x:H)⟫_ℂ=⟪(x:H),c • (x:H)⟫_ℂ at hh
    rw [hQx] at hh
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_smul_right, inner_self_eq_norm_sq_to_K, hx] at hh
    norm_num at hh
    exact hh.symm
  rw [hc1, one_smul] at hc
  intro y
  refine ⟨V.toContinuousLinearMap.adjoint y, ?_⟩
  exact congrArg (fun T : H →L[ℂ] H => T y) hc

/-- A concrete Fock unitary, constructed from the Gaussian projection rather
than assumed as a representation theorem. -/
theorem RegularWeyl.exists_fock_equiv [Nontrivial H]
    (hirr : ∀ T : H →L[ℂ] H,
      (∀ a, T.comp (W.operator a)=(W.operator a).comp T) →
        ∃ c : ℂ, T=c • ContinuousLinearMap.id ℂ H) :
    ∃ V : Fock d ≃ₗᵢ[ℂ] H, ∀ (a : Fin d → ℂ) (v : Fock d),
      W.operator a (V v)=V (displacement a v) := by
  obtain ⟨x,hx⟩ := W.exists_unit_vacuum
  let V := LinearIsometryEquiv.ofSurjective (W.vacuumEmbedding x hx)
    (W.vacuumEmbedding_surjective x hx hirr)
  refine ⟨V, ?_⟩
  intro a v
  exact (W.vacuumEmbedding_intertwines x hx a v).symm

end Cloning.WeylGNS
