import Cloning.PhysicalCloningConverseAdmissible
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Compact-window LAN estimates at two sample sizes and a converging output
scale. The fixed-window model continuity error is proved in the supremum norm. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.PhysicalCloningConverse
open Cloning.PCTPhysicalFidelity Cloning.PCTJointGaussianWhitening
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {k s : ℕ}

theorem parameterTranslation_smul (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (c : ℝ) (θ : Parameters k) : parameterTranslation p b e (c • θ) = c • parameterTranslation p b e θ := by
  apply Prod.ext
  · funext i
    simp [parameterTranslation, whiten, Finset.mul_sum, mul_div_assoc, mul_assoc, mul_left_comm]
  · rfl

theorem exists_uniform_model_scale_error (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (K : Set (Parameters k)) (hK : IsCompact K) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀)) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ n, ∀ θ ∈ K,
      ‖(model p b e (c n • θ)).1 - (model p b e (c₀ • θ)).1‖ ≤ η n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℝ → C(K, _) := fun t =>
    ⟨fun θ => (model p b e (t • θ.val)).1,
      (continuous_model p b e).comp (continuous_const.smul continuous_subtype_val)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_model p b e).comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  refine ⟨fun n => ‖F (c n)-F c₀‖, ?_, ?_⟩
  · simpa using (((hF.tendsto c₀).comp hc).sub_const (F c₀)).norm
  · intro n θ hθ
    exact ContinuousMap.norm_coe_le_norm (F (c n)-F c₀) ⟨θ,hθ⟩

/-- The same physical LAN channel sequences supply both sample-size
comparisons on a fixed window; no additional uniformity in the window is used. -/
theorem scaled_window_approximations
    (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin s ≃ PairIndex (k+1))
    (lan : CompactWindowLAN p b e)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀))
    (K : Set (Parameters k)) (hK : IsCompact K) (hzero : ∀ θ ∈ K, ∑ i, θ.1 i = 0) :
    ∃ δ η : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ θ ∈ K,
        ‖(lan.reverse n).map (model p b e θ).1 - chartTensor p θ n‖ ≤ δ n ∧
        ‖(lan.forward (m n)).map (chartTensor p (c n • θ) (m n)) -
          (model p b e (c₀ • θ)).1‖ ≤ η n := by
  let C := |c₀|+1
  let K' : Set (Parameters k) := (fun z : ℝ × Parameters k => z.1 • z.2) '' (Set.Icc (-C) C ×ˢ K)
  have hK' : IsCompact K' :=
    (isCompact_Icc.prod hK).image (continuous_fst.smul continuous_snd)
  have hz' : ∀ θ ∈ K', ∑ i, θ.1 i = 0 := by
    rintro θ ⟨⟨t,u⟩,hu,rfl⟩
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      hzero u hu.2, mul_zero]
  obtain ⟨δ,hδ,hδbound⟩ := lan.approximation K hK hzero
  obtain ⟨η,hη,hηbound⟩ := lan.approximation K' hK' hz'
  obtain ⟨ω,hω,hωbound⟩ := exists_uniform_model_scale_error p b e K hK c c₀ hc
  have htail : ∀ᶠ n in atTop, c n ∈ Set.Icc (-C) C := by
    filter_upwards [hc.norm.eventually_lt_const (show ‖c₀‖ < C by dsimp [C]; linarith)] with n hn
    simpa only [Set.mem_Icc, Real.norm_eq_abs, abs_le] using hn.le
  refine ⟨δ,fun n => η (m n)+ω n,hδ,by simpa using (hη.comp hm).add hω,?_⟩
  filter_upwards [hδbound,hm.eventually hηbound,htail] with n hd he ht θ hθ
  refine ⟨(hd θ hθ).2,?_⟩
  have hmem : c n • θ ∈ K' := ⟨(c n,θ),⟨ht,hθ⟩,rfl⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (model p b e (c n • θ)).1 _).trans
    (add_le_add (he (c n • θ) hmem).1 (hωbound n θ hθ))

end Cloning.PhysicalCloningConverse
