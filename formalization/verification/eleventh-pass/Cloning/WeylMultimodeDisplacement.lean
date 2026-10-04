import Cloning.WeylMultimodeKernel
import Cloning.WeylMultimodeDensity
import Cloning.WeylDisplacement

/-! Construction of the actual unitary Weyl displacement operators on finite-multimode Fock
space by completion of their coherent-vector action. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ}

lemma coherentCombination_dense : DenseRange (coherentCombination (d := d)) := by
  change Dense (Set.range (coherentCombination (d := d)))
  rw [← LinearMap.coe_range, coherentCombination, Finsupp.range_linearCombination]
  exact dense_coherentVector_span d

/-- A bounded linear Weyl operator constructed by extension from finite
coherent superpositions. -/
def displacement (a : Fin d → ℂ) : (Fock d) →L[ℂ] (Fock d) :=
  (displacedCombination a).extendOfNorm coherentCombination

lemma displacement_combination (a : Fin d → ℂ) (c : (Fin d → ℂ) →₀ ℂ) :
    displacement a (coherentCombination c) = displacedCombination a c := by
  apply LinearMap.extendOfNorm_eq coherentCombination_dense
  exact ⟨1, fun c => by simp [norm_displacedCombination]⟩

/-- Exact coherent-vector action of the constructed operator. -/
theorem displacement_coherentVector (a z : Fin d → ℂ) :
    displacement a (coherentVector z) =
      displacementPhase a z • coherentVector (a + z) := by
  have h := displacement_combination a (Finsupp.single z 1)
  simpa [coherentCombination, displacedCombination, displacedCoherent] using h

/-- The constructed Weyl operator preserves norms on the entire multimode Fock space. -/
theorem displacement_norm (a : Fin d → ℂ) (v : (Fock d)) : ‖displacement a v‖ = ‖v‖ := by
  refine coherentCombination_dense.induction_on (p := fun v => ‖displacement a v‖ = ‖v‖) v
    (isClosed_eq ((displacement a).continuous.norm) continuous_norm) ?_
  intro c
  rw [displacement_combination, norm_displacedCombination]

/-- Bounded linear maps on the multimode Fock space are determined by their coherent action. -/
theorem continuousLinearMap_ext_coherent {T S : (Fock d) →L[ℂ] (Fock d)}
    (h : ∀ z : Fin d → ℂ, T (coherentVector z) = S (coherentVector z)) : T = S := by
  have he : (fun v => T v) = (fun v => S v) := by
    apply coherentCombination_dense.equalizer T.continuous S.continuous
    funext c
    simp only [Function.comp_apply, coherentCombination, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum, map_smul, h]
  exact DFunLike.ext _ _ (congrFun he)

/-- The Weyl multiplication relation for actual bounded operators. -/
theorem displacement_comp (a b : Fin d → ℂ) :
    (displacement a).comp (displacement b) =
      displacementPhase a b • displacement (a + b) := by
  apply continuousLinearMap_ext_coherent
  intro z
  simp only [ContinuousLinearMap.comp_apply, displacement_coherentVector,
    map_smul, ContinuousLinearMap.smul_apply, smul_smul, displacementPhase_cocycle,
    add_assoc]

@[simp] theorem displacement_zero : displacement (0 : Fin d → ℂ) = ContinuousLinearMap.id ℂ (Fock d) := by
  apply continuousLinearMap_ext_coherent
  intro z
  simp [displacement_coherentVector]

@[simp] theorem displacementPhase_neg (a : Fin d → ℂ) : displacementPhase (-a) a = 1 := by
  simp [displacementPhase]

@[simp] theorem displacementPhase_neg_right (a : Fin d → ℂ) : displacementPhase a (-a) = 1 := by
  simp [displacementPhase]

@[simp] theorem displacement_neg_cancel (a : Fin d → ℂ) (v : (Fock d)) :
    displacement (-a) (displacement a v) = v := by
  have h := congrArg (fun T : (Fock d) →L[ℂ] (Fock d) => T v) (displacement_comp (-a) a)
  simpa using h

@[simp] theorem displacement_cancel_neg (a : Fin d → ℂ) (v : (Fock d)) :
    displacement a (displacement (-a) v) = v := by
  simpa only [neg_neg] using displacement_neg_cancel (-a) v

/-- The Weyl displacement is a complex-linear unitary on the actual multimode Fock
Hilbert space, with inverse the negative displacement. -/
def weylUnitary (a : Fin d → ℂ) : (Fock d) ≃ₗᵢ[ℂ] (Fock d) where
  toLinearEquiv :=
    { toFun := displacement a
      invFun := displacement (-a)
      left_inv := displacement_neg_cancel a
      right_inv := displacement_cancel_neg a
      map_add' := map_add (displacement a)
      map_smul' := map_smul (displacement a) }
  norm_map' := displacement_norm a

@[simp] theorem weylUnitary_apply (a : Fin d → ℂ) (v : (Fock d)) :
    weylUnitary a v = displacement a v := rfl

@[simp] theorem weylUnitary_symm (a : Fin d → ℂ) : (weylUnitary a).symm = weylUnitary (-a) := by
  ext v
  rfl

end Cloning.MultimodeCoherent
