import Cloning.WeylGNSRegular
import Cloning.WeylIdlerKernel
import Cloning.UniversalLeastNoiseQuantumKernel

/-! The Hilbert space associated to an actual continuous positive Weyl
characteristic function, and the isometric translation of its kernel vectors. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.WeylGNS
open MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ}

def kernel (g : (Fin d → ℂ) → ℂ) (a b : Fin d → ℂ) : ℂ :=
  displacementPhase (-a) b * g (b - a)

theorem kernel_eq_quantumPositiveKernel (g : (Fin d → ℂ) → ℂ) :
    kernel g = quantumPositiveKernel g 0 := by
  funext a b
  simp [kernel, quantumPositiveKernel]

theorem normalizedPositive_kernel {g : (Fin d → ℂ) → ℂ}
    (hg : IsWeylCharacteristicPositive g) (hg0 : g 0 = 1) :
    PositiveKernel.IsNormalizedPositive (kernel g) := by
  have hp : IsQuantumPositive g 0 := by
    intro n b c
    simpa only [← kernel_eq_quantumPositiveKernel, kernel] using hg n b c
  rw [kernel_eq_quantumPositiveKernel]
  exact hp.normalizedPositiveKernel hg0

theorem continuous_kernel {g : (Fin d → ℂ) → ℂ} (hg : Continuous g) :
    Continuous (fun p : (Fin d → ℂ) × (Fin d → ℂ) => kernel g p.1 p.2) := by
  unfold kernel displacementPhase ComplexCoherent.displacementPhase
  apply Continuous.mul
  · fun_prop
  · exact hg.comp (continuous_snd.sub continuous_fst)

theorem phase_kernel_translate (g : (Fin d → ℂ) → ℂ) (z a b : Fin d → ℂ) :
    star (displacementPhase z a) * displacementPhase z b *
      kernel g (z + a) (z + b) = kernel g a b := by
  have hp : star (displacementPhase z a) * displacementPhase z b *
      displacementPhase (-(z + a)) (z + b) = displacementPhase (-a) b := by
    change (starRingEnd ℂ) (displacementPhase z a) * displacementPhase z b *
      displacementPhase (-(z + a)) (z + b) = displacementPhase (-a) b
    simp only [displacementPhase, map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [ComplexCoherent.displacementPhase, Pi.neg_apply, Pi.add_apply,
      ← Complex.exp_conj, ← Complex.exp_add, map_div₀, map_sub, map_add,
      map_neg, map_mul, map_ofNat, starRingEnd_self_apply]
    congr 1
    ring
  unfold kernel
  rw [← mul_assoc, hp]
  congr 1
  abel

variable (g : (Fin d → ℂ) → ℂ) [Fact (PositiveKernel.IsNormalizedPositive (kernel g))]

abbrev Space := PositiveKernel.Space (kernel g)

def feature (a : Fin d → ℂ) : Space g := PositiveKernel.feature (kernel g) a

@[simp] theorem inner_feature (a b : Fin d → ℂ) :
    ⟪feature g a, feature g b⟫_ℂ = kernel g a b :=
  PositiveKernel.inner_feature (kernel g) a b

@[simp] theorem norm_feature (a : Fin d → ℂ) : ‖feature g a‖ = 1 :=
  PositiveKernel.norm_feature (kernel g) a

def combination : ((Fin d → ℂ) →₀ ℂ) →ₗ[ℂ] Space g :=
  Finsupp.linearCombination ℂ (feature g)

theorem combination_eq_coe (c : (Fin d → ℂ) →₀ ℂ) :
    combination g c = UniformSpace.Completion.coe'
      (show PositiveKernel.PreSpace (kernel g) from c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => exact (map_zero (combination g)).trans (UniformSpace.Completion.coe_zero).symm
  | add c e hc he =>
      rw [map_add, hc, he]
      exact (UniformSpace.Completion.coe_add _ _).symm
  | single a t =>
      simp only [combination, Finsupp.linearCombination_single]
      change t • UniformSpace.Completion.coe'
        (show PositiveKernel.PreSpace (kernel g) from Finsupp.single a 1) = _
      rw [← UniformSpace.Completion.coe_smul]
      congr 1
      exact Finsupp.smul_single t a (1 : ℂ) |>.trans (by simp)

theorem combination_dense : DenseRange (combination g) := by
  have h := UniformSpace.Completion.denseRange_coe
    (α := PositiveKernel.PreSpace (kernel g))
  have he : (combination g : ((Fin d → ℂ) →₀ ℂ) → Space g) =
      fun c => UniformSpace.Completion.coe'
        (show PositiveKernel.PreSpace (kernel g) from c) := funext (combination_eq_coe g)
  rw [he]
  exact h

def translatedFeature (z a : Fin d → ℂ) : Space g :=
  displacementPhase z a • feature g (z + a)

theorem inner_translatedFeature (z a b : Fin d → ℂ) :
    ⟪translatedFeature g z a, translatedFeature g z b⟫_ℂ =
      ⟪feature g a, feature g b⟫_ℂ := by
  simp only [translatedFeature, inner_smul_left, inner_smul_right, inner_feature]
  simpa only [starRingEnd_apply, mul_assoc, mul_left_comm] using phase_kernel_translate g z a b

def translatedCombination (z : Fin d → ℂ) : ((Fin d → ℂ) →₀ ℂ) →ₗ[ℂ] Space g :=
  Finsupp.linearCombination ℂ (translatedFeature g z)

theorem inner_translatedCombination (z : Fin d → ℂ) (c e : (Fin d → ℂ) →₀ ℂ) :
    ⟪translatedCombination g z c, translatedCombination g z e⟫_ℂ =
      ⟪combination g c, combination g e⟫_ℂ := by
  simp only [translatedCombination, combination, Finsupp.linearCombination_apply,
    Finsupp.sum, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    inner_translatedFeature]

theorem norm_translatedCombination (z : Fin d → ℂ) (c : (Fin d → ℂ) →₀ ℂ) :
    ‖translatedCombination g z c‖ = ‖combination g c‖ := by
  have h := congrArg Complex.re (inner_translatedCombination g z c c)
  change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _ at h
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  nlinarith [norm_nonneg (translatedCombination g z c), norm_nonneg (combination g c)]

end Cloning.WeylGNS
