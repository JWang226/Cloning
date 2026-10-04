import Cloning.TensorFlatProjectorCasimirTrace
import Cloning.Projector

/-! Sharp quadratic tightness for the actual physical flat Young law. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT Cloning.YoungGeneral MvPolynomial
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Grouping an observable over the literal physical copies. -/
theorem physicalYoungPMF_sum_observable (L : List (PhysicalHighestTensor n d))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤)
    (p : Fin d → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (f : (Fin d → ℕ) → ℝ) :
    ∑ mu : Shape d n, (physicalYoungPMF L hL hspan p hp hs mu).toReal *
      f (fun a => (mu a).val) = ∑ i : Fin L.length, (L.get i).character p * f (L.get i).weight := by
  classical
  simp only [physicalYoungPMF_toReal, ← physicalLabelMass_eq_count_mul,
    physicalLabelMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul, ← PhysicalHighestTensor.shape_eq_iff]
  simp [PhysicalHighestTensor.shape]

/-- The Casimir trace evaluated on the flat input, expressed in its actual
orthogonal physical summands. -/
theorem flat_casimir_trace_eq_sum_blocks (L : List (PhysicalHighestTensor n d))
    (hL : OrthogonalFamily ℂ (fun i : Fin L.length => (L.get i).sector)
      (fun i => (L.get i).sector.subtypeₗᵢ))
    (hspan : (⨆ i : Fin L.length, (L.get i).sector) = ⊤) (c : ℝ) (hc : 0 ≤ c) :
    eval (fun _ : Fin d => (c : ℂ)) (tensorWeightTrace (collectiveCasimir n d)) =
      ∑ i : Fin L.length, ((L.get i).character (fun _ => c) : ℂ) *
        casimirEigenvalue (fun a => ((L.get i).weight a : ℂ)) := by
  classical
  rw [eval_tensorWeightTrace, LinearMap.trace_eq_sum_inner _ (physicalSchurBasis L hL hspan)]
  simp only [physicalSchurBasis_apply, PhysicalSchurBasisIndex, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  let H := L.get i
  have hm (j : PartitionIndex H.weight H.weight_antitone) :
      physicalSchurBasisVector L ⟨i,j⟩ ∈ cyclicSector H.vector :=
    (H.canonicalIsometry (partitionBasis H.weight H.weight_antitone j)).property
  have he (j : PartitionIndex H.weight H.weight_antitone) :
      ⟪physicalSchurBasisVector L ⟨i,j⟩,
        (tensorOperator n (Matrix.diagonal (fun _ : Fin d => (c : ℂ))) *
          collectiveCasimir n d) (physicalSchurBasisVector L ⟨i,j⟩)⟫_ℂ =
        (c : ℂ)^n * casimirEigenvalue (fun a => (H.weight a : ℂ)) := by
    rw [ContinuousLinearMap.mul_apply, collectiveCasimir_eq_smul_on_cyclicSector
      H.vector (fun a => (H.weight a : ℂ)) H.cartan H.raising (hm j), map_smul]
    have ht : tensorOperator n (Matrix.diagonal (fun _ : Fin d => (c : ℂ)))
        (physicalSchurBasisVector L ⟨i,j⟩) = (c : ℂ)^n • physicalSchurBasisVector L ⟨i,j⟩ := by
      apply lp.ext
      funext w
      rw [tensorOperator_diagonal_apply]
      simp
    rw [ht, inner_smul_right, inner_smul_right]
    have hn := orthonormal_iff_ite.mp (physicalSchurBasisVector_orthonormal L hL) ⟨i,j⟩ ⟨i,j⟩
    simp only [if_true] at hn
    rw [hn]
    ring
  simp only [ContinuousLinearMap.coe_coe, he, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  change _ = (H.character (fun _ => c) : ℂ) * _
  unfold PhysicalHighestTensor.character
  rw [sectorPartitionFunction_const _ _ _ _ c hc]
  change _ = ((c ^ (∑ a, H.weight a) * (partitionDimension H.weight H.weight_antitone : ℝ) : ℝ) : ℂ) * _
  rw [H.weight_sum]
  simp only [PartitionIndex, Fintype.card_fin]
  push_cast
  ring

/-- The exact quadratic Casimir moment of the actual flat Young PMF. -/
theorem tensorFlatYoungPMF_casimir_moment (hd : 0 < d) :
    ∑ mu : Shape d n, (tensorFlatYoungPMF n d hd mu).toReal *
      (casimirEigenvalue (fun a => ((mu a).val : ℂ))).re =
      (n : ℝ)*(d : ℝ) + (n : ℝ)*((n : ℝ)-1)/(d : ℝ) := by
  let L := recursivePhysicalDecomposition n d
  have hL := (recursivePhysicalDecomposition_is_decomposition n d).1
  have hspan := (recursivePhysicalDecomposition_is_decomposition n d).2
  change ∑ mu : Shape d n, (physicalYoungPMF L hL hspan (flatSpectrum d)
    (fun _ => by unfold flatSpectrum; positivity) (flatSpectrum_sum d hd) mu).toReal * _ = _
  rw [physicalYoungPMF_sum_observable (f := fun mu =>
    (casimirEigenvalue (fun a => (mu a : ℂ))).re)]
  have he := flat_casimir_trace_eq_sum_blocks L hL hspan (1/(d:ℝ)) (by positivity)
  rw [tensor_flat_casimir_expectation hd] at he
  have hr := congrArg Complex.re he
  have hc : ((n:ℂ)*(d:ℂ)+(n:ℂ)*((n:ℂ)-1)/(d:ℂ)).re =
      (n:ℝ)*(d:ℝ)+(n:ℝ)*((n:ℝ)-1)/(d:ℝ) := by
    have hc : (n:ℂ)*(d:ℂ)+(n:ℂ)*((n:ℂ)-1)/(d:ℂ) =
        (((n:ℝ)*(d:ℝ)+(n:ℝ)*((n:ℝ)-1)/(d:ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.ofReal_re]
  rw [hc] at hr
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  exact hr.symm

/-- Real form of the genuine tensor Casimir eigenvalue. -/
theorem casimirEigenvalue_nat_re (mu : Fin d → ℕ) :
    (casimirEigenvalue (fun a => (mu a : ℂ))).re =
      ∑ a, (mu a : ℝ)^2 + ∑ a, ∑ b, if a < b then (mu a : ℝ) - mu b else 0 := by
  simp [casimirEigenvalue, Complex.mul_re, pow_two, apply_ite]

/-- The physical flat Young law has the sharp O(n) centered second moment.
No character, Casimir or probability identity is assumed. -/
theorem tensorFlatYoungPMF_centered_second_moment_le (hd : 0 < d) :
    (∑ mu : Shape d n, (tensorFlatYoungPMF n d hd mu).toReal *
      (∑ a : Fin d, (((mu a).val : ℝ) - (n : ℝ)/(d : ℝ))^2)) ≤
      (n : ℝ) * ((d : ℝ) - 1/(d : ℝ)) := by
  classical
  let L := recursivePhysicalDecomposition n d
  have hL := (recursivePhysicalDecomposition_is_decomposition n d).1
  have hspan := (recursivePhysicalDecomposition_is_decomposition n d).2
  have hp : ∀ a, 0 ≤ flatSpectrum d a := fun _ => by unfold flatSpectrum; positivity
  have hs := flatSpectrum_sum d hd
  have ht := tensorFlatYoungPMF_casimir_moment (n := n) hd
  change ∑ mu : Shape d n, (physicalYoungPMF L hL hspan (flatSpectrum d) hp hs mu).toReal * _ = _ at ht
  rw [physicalYoungPMF_sum_observable (f := fun mu =>
    (casimirEigenvalue (fun a => (mu a : ℂ))).re)] at ht
  change (∑ mu : Shape d n, (physicalYoungPMF L hL hspan (flatSpectrum d) hp hs mu).toReal * _) ≤ _
  rw [physicalYoungPMF_sum_observable (f := fun mu =>
    ∑ a : Fin d, ((mu a : ℝ) - (n : ℝ)/(d : ℝ))^2)]
  apply Cloning.Projector.second_moment_le_of_casimir Finset.univ
    (fun i : Fin L.length => (L.get i).character (flatSpectrum d))
    (fun i => ∑ a : Fin d, (((L.get i).weight a : ℝ) - (n : ℝ)/(d : ℝ))^2)
    (fun i => ∑ a : Fin d, ∑ b : Fin d, if a < b then
      ((L.get i).weight a : ℝ) - (L.get i).weight b else 0)
    (fun i => (casimirEigenvalue (fun a => ((L.get i).weight a : ℂ))).re)
    (n : ℝ) (d : ℝ)
  · intro i _
    exact (L.get i).character_nonneg _
  · rw [sum_physical_characters L hL hspan _ hp, hs, one_pow]
  · intro i _
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    split_ifs with hab
    · exact sub_nonneg.mpr (by exact_mod_cast (L.get i).weight_antitone hab.le)
    · exact le_rfl
  · intro i _
    rw [casimirEigenvalue_nat_re]
    have hsum : ∑ a : Fin d, ((L.get i).weight a : ℝ) = n := by
      exact_mod_cast (L.get i).weight_sum
    rw [Cloning.Projector.centered_square_sum_eq Finset.univ
      (fun a : Fin d => ((L.get i).weight a : ℝ)) (n : ℝ) (d : ℝ)
      (Nat.cast_ne_zero.mpr hd.ne') (by simp) hsum]
    ring
  · exact ht

end Cloning.TensorLie
