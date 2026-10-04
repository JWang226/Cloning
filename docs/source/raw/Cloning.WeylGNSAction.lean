import Cloning.WeylGNSKernel

/-! A normalized continuous positive Weyl characteristic has a genuine cyclic
regular Weyl representation on its completed kernel space. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.WeylGNS
open MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ} (g : (Fin d → ℂ) → ℂ)
  [Fact (PositiveKernel.IsNormalizedPositive (kernel g))]

def action (a : Fin d → ℂ) : Space g →L[ℂ] Space g :=
  (translatedCombination g a).extendOfNorm (combination g)

theorem action_combination (a : Fin d → ℂ) (c : (Fin d → ℂ) →₀ ℂ) :
    action g a (combination g c) = translatedCombination g a c := by
  apply LinearMap.extendOfNorm_eq (combination_dense g)
  exact ⟨1, fun c => by simp [norm_translatedCombination]⟩

theorem action_feature (a z : Fin d → ℂ) :
    action g a (feature g z) = displacementPhase a z • feature g (a + z) := by
  have h := action_combination g a (Finsupp.single z 1)
  simpa [combination, translatedCombination, translatedFeature] using h

theorem action_norm (a : Fin d → ℂ) (v : Space g) : ‖action g a v‖ = ‖v‖ := by
  refine (combination_dense g).induction_on (p := fun v => ‖action g a v‖ = ‖v‖) v
    (isClosed_eq ((action g a).continuous.norm) continuous_norm) ?_
  intro c
  rw [action_combination, norm_translatedCombination]

theorem continuousLinearMap_ext_feature {T S : Space g →L[ℂ] Space g}
    (h : ∀ z : Fin d → ℂ, T (feature g z) = S (feature g z)) : T = S := by
  have he : (fun v => T v) = (fun v => S v) := by
    apply (combination_dense g).equalizer T.continuous S.continuous
    funext c
    simp only [Function.comp_apply, combination, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum, map_smul, h]
  exact DFunLike.ext _ _ (congrFun he)

theorem action_comp (a b : Fin d → ℂ) :
    (action g a).comp (action g b) = displacementPhase a b • action g (a + b) := by
  apply continuousLinearMap_ext_feature
  intro z
  simp only [ContinuousLinearMap.comp_apply, action_feature, map_smul,
    ContinuousLinearMap.smul_apply, smul_smul, displacementPhase_cocycle, add_assoc]

@[simp] theorem action_zero : action g 0 = ContinuousLinearMap.id ℂ (Space g) := by
  apply continuousLinearMap_ext_feature
  intro z
  simp [action_feature]

@[simp] theorem action_neg_cancel (a : Fin d → ℂ) (v : Space g) :
    action g (-a) (action g a v) = v := by
  have h := congrArg (fun T : Space g →L[ℂ] Space g => T v) (action_comp g (-a) a)
  simpa using h

@[simp] theorem action_cancel_neg (a : Fin d → ℂ) (v : Space g) :
    action g a (action g (-a) v) = v := by
  simpa only [neg_neg] using action_neg_cancel g (-a) v

def unitary (a : Fin d → ℂ) : Space g ≃ₗᵢ[ℂ] Space g where
  toLinearEquiv :=
    { toFun := action g a
      invFun := action g (-a)
      left_inv := action_neg_cancel g a
      right_inv := action_cancel_neg g a
      map_add' := map_add (action g a)
      map_smul' := map_smul (action g a) }
  norm_map' := action_norm g a

@[simp] theorem unitary_apply (a : Fin d → ℂ) (v : Space g) :
    unitary g a v = action g a v := rfl

@[simp] theorem action_dist (a : Fin d → ℂ) (v w : Space g) :
    dist (action g a v) (action g a w) = dist v w := by
  simp only [dist_eq_norm, ← map_sub, action_norm]

theorem continuous_action_feature (hg : Continuous g) (z : Fin d → ℂ) :
    Continuous (fun a => action g a (feature g z)) := by
  simp_rw [action_feature]
  exact (continuous_displacementPhase z).smul
    ((PositiveKernel.continuous_feature (kernel g) (continuous_kernel hg)).comp
      (continuous_id.add continuous_const))

theorem continuous_action_combination (hg : Continuous g) (c : (Fin d → ℂ) →₀ ℂ) :
    Continuous (fun a => action g a (combination g c)) := by
  simp only [combination, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  exact continuous_finset_sum _ (fun z _ =>
    continuous_const.smul (continuous_action_feature g hg z))

theorem continuous_action (hg : Continuous g) (v : Space g) :
    Continuous (fun a => action g a v) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  obtain ⟨c, hc⟩ := (combination_dense g).exists_dist_lt v (show 0 < ε / 4 by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuous_iff.mp (continuous_action_combination g hg c)
    a (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hb' := hd b hb
  calc
    dist (action g b v) (action g a v) ≤
        dist (action g b v) (action g b (combination g c)) +
          dist (action g b (combination g c)) (action g a (combination g c)) +
          dist (action g a (combination g c)) (action g a v) := dist_triangle4 _ _ _ _
    _ < ε := by
      rw [action_dist, action_dist, dist_comm (combination g c) v]
      linarith

/-- The actual GNS action with proved strong continuity. -/
def regularWeyl (hg : Continuous g) : RegularWeyl d (Space g) where
  toIsometry := unitary g
  zero_apply := by intro v; simp
  mul_apply := by
    intro a b v
    exact congrArg (fun T : Space g →L[ℂ] Space g => T v) (action_comp g a b)
  continuous_apply := continuous_action g hg

@[simp] theorem action_origin (a : Fin d → ℂ) :
    action g a (feature g 0) = feature g a := by simp [action_feature]

theorem origin_characteristic (a : Fin d → ℂ) :
    ⟪feature g 0, action g a (feature g 0)⟫_ℂ = g a := by
  simp [kernel]

theorem feature_dense_span :
    (Submodule.span ℂ (Set.range (feature g))).topologicalClosure = ⊤ := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  have h := combination_dense g
  change Dense (Set.range (combination g)) at h
  rw [← LinearMap.coe_range, combination, Finsupp.range_linearCombination] at h
  exact h

/-- The unit vector at the origin is cyclic. -/
theorem origin_cyclic :
    (Submodule.span ℂ (Set.range (fun a : Fin d → ℂ => action g a (feature g 0)))).topologicalClosure
      = ⊤ := by
  simpa only [action_origin] using feature_dense_span g

end Cloning.WeylGNS
