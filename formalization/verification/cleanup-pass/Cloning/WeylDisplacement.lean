import Cloning.WeylKernel
import Cloning.WeylDensity

/-! Construction of the actual unitary Weyl displacement operators on Fock
space by completion of their coherent-vector action. -/

noncomputable section
open scoped InnerProductSpace Topology BigOperators

namespace Cloning.ComplexCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

lemma coherentCombination_dense : DenseRange coherentCombination := by
  change Dense (Set.range coherentCombination)
  rw [← LinearMap.coe_range, coherentCombination, Finsupp.range_linearCombination]
  exact dense_coherentVector_span

/-- A bounded linear Weyl operator constructed by extension from finite
coherent superpositions. -/
def displacement (a : ℂ) : Fock →L[ℂ] Fock :=
  (displacedCombination a).extendOfNorm coherentCombination

lemma displacement_combination (a : ℂ) (c : ℂ →₀ ℂ) :
    displacement a (coherentCombination c) = displacedCombination a c := by
  apply LinearMap.extendOfNorm_eq coherentCombination_dense
  exact ⟨1, fun c => by simp [norm_displacedCombination]⟩

/-- Exact coherent-vector action of the constructed operator. -/
theorem displacement_coherentVector (a z : ℂ) :
    displacement a (coherentVector z) =
      displacementPhase a z • coherentVector (a + z) := by
  have h := displacement_combination a (Finsupp.single z 1)
  simpa [coherentCombination, displacedCombination, displacedCoherent] using h

/-- The constructed Weyl operator preserves norms on the entire Fock space. -/
theorem displacement_norm (a : ℂ) (v : Fock) : ‖displacement a v‖ = ‖v‖ := by
  refine coherentCombination_dense.induction_on (p := fun v => ‖displacement a v‖ = ‖v‖) v
    (isClosed_eq ((displacement a).continuous.norm) continuous_norm) ?_
  intro c
  rw [displacement_combination, norm_displacedCombination]

/-- Bounded linear maps on Fock space are determined by their coherent action. -/
theorem continuousLinearMap_ext_coherent {T S : Fock →L[ℂ] Fock}
    (h : ∀ z : ℂ, T (coherentVector z) = S (coherentVector z)) : T = S := by
  have he : (fun v => T v) = (fun v => S v) := by
    apply coherentCombination_dense.equalizer T.continuous S.continuous
    funext c
    simp only [Function.comp_apply, coherentCombination, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum, map_smul, h]
  exact DFunLike.ext _ _ (congrFun he)

/-- The Weyl multiplication relation for actual bounded operators. -/
theorem displacement_comp (a b : ℂ) :
    (displacement a).comp (displacement b) =
      displacementPhase a b • displacement (a + b) := by
  apply continuousLinearMap_ext_coherent
  intro z
  simp only [ContinuousLinearMap.comp_apply, displacement_coherentVector,
    map_smul, ContinuousLinearMap.smul_apply, smul_smul, displacementPhase_cocycle,
    add_assoc]

@[simp] theorem displacement_zero : displacement 0 = ContinuousLinearMap.id ℂ Fock := by
  apply continuousLinearMap_ext_coherent
  intro z
  simp [displacement_coherentVector]

@[simp] theorem displacementPhase_neg (a : ℂ) : displacementPhase (-a) a = 1 := by
  simp [displacementPhase, map_neg, mul_comm a (starRingEnd ℂ a)]

@[simp] theorem displacementPhase_neg_right (a : ℂ) : displacementPhase a (-a) = 1 := by
  simp [displacementPhase, map_neg, mul_comm a (starRingEnd ℂ a)]

@[simp] theorem displacement_neg_cancel (a : ℂ) (v : Fock) :
    displacement (-a) (displacement a v) = v := by
  have h := congrArg (fun T : Fock →L[ℂ] Fock => T v) (displacement_comp (-a) a)
  simpa using h

@[simp] theorem displacement_cancel_neg (a : ℂ) (v : Fock) :
    displacement a (displacement (-a) v) = v := by
  simpa only [neg_neg] using displacement_neg_cancel (-a) v

/-- The Weyl displacement is a complex-linear unitary on the actual Fock
Hilbert space, with inverse the negative displacement. -/
def weylUnitary (a : ℂ) : Fock ≃ₗᵢ[ℂ] Fock where
  toLinearEquiv :=
    { toFun := displacement a
      invFun := displacement (-a)
      left_inv := displacement_neg_cancel a
      right_inv := displacement_cancel_neg a
      map_add' := map_add (displacement a)
      map_smul' := map_smul (displacement a) }
  norm_map' := displacement_norm a

@[simp] theorem weylUnitary_apply (a : ℂ) (v : Fock) :
    weylUnitary a v = displacement a v := rfl

@[simp] theorem weylUnitary_symm (a : ℂ) : (weylUnitary a).symm = weylUnitary (-a) := by
  ext v
  rfl

end Cloning.ComplexCoherent
