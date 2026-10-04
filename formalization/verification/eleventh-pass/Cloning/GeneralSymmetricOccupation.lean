import Cloning.SymmetricOccupation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Arbitrary-dimensional symmetric tensors in the computational basis

The ambient space has computational words `Fin L → Fin d`. Occupations are
actual multiplicity profiles of words. We prove that these profiles classify
slot-permutation orbits and that the normalized uniform vectors on their
fibers form an orthonormal family. The range of the resulting isometry is
exactly the permutation-invariant (symmetric tensor) subspace.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace

namespace Cloning.GeneralSymmetricOccupation

abbrev Word (L d : ℕ) := Fin L → Fin d
abbrev TensorSpace (L d : ℕ) := lp (fun _ : Word L d => ℂ) 2

/-- Multiplicity of each one-particle basis vector in a computational tensor. -/
def profile {L d : ℕ} (w : Word L d) (a : Fin d) : ℕ :=
  Fintype.card {i : Fin L // w i = a}

/-- Realized occupation profiles; no nonemptiness assumption on a fiber is hidden. -/
def Occupation (L d : ℕ) := Set.range (@profile L d)

instance (L d : ℕ) : Fintype (Occupation L d) := by
  unfold Occupation
  exact Fintype.ofFinite _
instance (L d : ℕ) : DecidableEq (Occupation L d) := Classical.decEq _

/-- The occupation associated to a computational word. -/
def label {L d : ℕ} (w : Word L d) : Occupation L d := ⟨profile w, ⟨w, rfl⟩⟩

theorem label_surjective (L d : ℕ) : Function.Surjective (@label L d) := by
  rintro ⟨q, w, hw⟩
  exact ⟨w, Subtype.ext hw⟩

/-- Equal occupations are precisely equivalent under permutation of the tensor slots. -/
theorem profile_eq_iff_perm {L d : ℕ} (w z : Word L d) :
    profile w = profile z ↔ ∃ σ : Equiv.Perm (Fin L), ∀ i, z (σ i) = w i := by
  classical
  constructor
  · intro h
    let e (a : Fin d) : {i : Fin L // w i = a} ≃ {i : Fin L // z i = a} :=
      Fintype.equivOfCardEq (congrFun h a)
    exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  · rintro ⟨σ, hσ⟩
    funext a
    exact Fintype.card_congr
      { toFun := fun i => ⟨σ i, (hσ i).trans i.property⟩
        invFun := fun i => ⟨σ.symm i, by rw [← hσ, σ.apply_symm_apply]; exact i.property⟩
        left_inv := fun i => by simp
        right_inv := fun i => by simp }

theorem label_eq_iff_perm {L d : ℕ} (w z : Word L d) :
    label w = label z ↔ ∃ σ : Equiv.Perm (Fin L), ∀ i, z (σ i) = w i := by
  rw [← profile_eq_iff_perm]
  exact Subtype.ext_iff

theorem profile_permute {L d : ℕ} (w : Word L d) (σ : Equiv.Perm (Fin L)) :
    profile (w ∘ σ) = profile w :=
  (profile_eq_iff_perm _ _).mpr ⟨σ, fun _ => rfl⟩

@[simp] theorem label_permute {L d : ℕ} (w : Word L d) (σ : Equiv.Perm (Fin L)) :
    label (w ∘ σ) = label w := Subtype.ext (profile_permute w σ)

/-- Number of computational words of an occupation. -/
def multiplicity {L d : ℕ} (q : Occupation L d) : ℕ :=
  (Finset.univ.filter (fun w : Word L d => label w = q)).card

theorem multiplicity_pos {L d : ℕ} (q : Occupation L d) : 0 < multiplicity q := by
  obtain ⟨w, hw⟩ := label_surjective L d q
  exact Finset.card_pos.mpr ⟨w, by simp [hw]⟩

def weight {L d : ℕ} (q : Occupation L d) (w : Word L d) : ℝ :=
  if label w = q then (multiplicity q : ℝ)⁻¹ else 0

theorem weight_nonneg {L d : ℕ} (q : Occupation L d) (w : Word L d) :
    0 ≤ weight q w := by unfold weight; split_ifs <;> positivity

theorem weight_hasSum {L d : ℕ} (q : Occupation L d) : HasSum (weight q) 1 := by
  classical
  have hm : (multiplicity q : ℝ) ≠ 0 := by exact_mod_cast (multiplicity_pos q).ne'
  have hs : ∑ w : Word L d, weight q w = 1 := by
    simp only [weight, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hm
  exact hs ▸ hasSum_fintype _

/-- Normalized uniform occupation vector in the physical computational tensor basis. -/
def column {L d : ℕ} (q : Occupation L d) : TensorSpace L d :=
  Cloning.CoherentCoefficients.amplitudeVector (weight q) (weight_nonneg q) (weight_hasSum q)

theorem column_apply {L d : ℕ} (q : Occupation L d) (w : Word L d) :
    column q w = if label w = q then
      ((Real.sqrt (multiplicity q : ℝ))⁻¹ : ℂ) else 0 := by
  simp only [column, Cloning.CoherentCoefficients.amplitudeVector_apply, weight]
  split_ifs <;> simp [Real.sqrt_inv]

theorem column_norm {L d : ℕ} (q : Occupation L d) : ‖column q‖ = 1 :=
  Cloning.CoherentCoefficients.amplitudeVector_norm _ _ _

theorem column_orthonormal (L d : ℕ) : Orthonormal ℂ (@column L d) := by
  refine ⟨column_norm, ?_⟩
  intro q r hqr
  rw [lp.inner_eq_tsum]
  have hz : ∀ w : Word L d, ⟪column q w, column r w⟫_ℂ = 0 := by
    intro w
    rw [column_apply, column_apply]
    split_ifs with hq hr
    · exact False.elim (hqr (hq.symm.trans hr))
    all_goals simp
  simp only [hz, tsum_zero]

abbrev OccupationSpace (L d : ℕ) := lp (fun _ : Occupation L d => ℂ) 2

/-- Occupation coordinates embedded into the actual finite tensor product. -/
def isometry (L d : ℕ) : OccupationSpace L d →ₗᵢ[ℂ] TensorSpace L d :=
  (column_orthonormal L d).orthogonalFamily.linearIsometry

theorem isometry_single (L d : ℕ) (q : Occupation L d) :
    isometry L d (lp.single 2 q 1) = column q := by
  rw [isometry, OrthogonalFamily.linearIsometry_apply_single]
  exact one_smul ℂ _

theorem isometry_apply {L d : ℕ} (v : OccupationSpace L d) (w : Word L d) :
    isometry L d v w = v (label w) / (Real.sqrt (multiplicity (label w) : ℝ) : ℂ) := by
  classical
  have hs : isometry L d v = ∑ q : Occupation L d, v q • column q := by
    rw [isometry, OrthogonalFamily.linearIsometry_apply, tsum_fintype]
    rfl
  rw [hs]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (label w)]
  · simp [column_apply, div_eq_mul_inv]
  · intro q hq hn
    simp [column_apply, Ne.symm hn]
  · simp

/-- Symmetric tensors are the fixed vectors of every permutation of tensor slots. -/
def symmetricSubspace (L d : ℕ) : Submodule ℂ (TensorSpace L d) where
  carrier := {v | ∀ (w : Word L d) (σ : Equiv.Perm (Fin L)), v (w ∘ σ) = v w}
  zero_mem' := by intro w σ; rfl
  add_mem' := by intro v u hv hu w σ; exact congrArg₂ (· + ·) (hv w σ) (hu w σ)
  smul_mem' := by intro a v hv w σ; exact congrArg (a • ·) (hv w σ)

theorem symmetric_iff_constant_on_fibers {L d : ℕ} (v : TensorSpace L d) :
    v ∈ symmetricSubspace L d ↔ ∀ w z : Word L d, label w = label z → v w = v z := by
  constructor
  · intro hv w z h
    obtain ⟨σ, hσ⟩ := (label_eq_iff_perm w z).mp h
    have hw : z ∘ σ = w := funext hσ
    simpa only [hw] using hv z σ
  · intro hv w σ
    exact hv _ _ (label_permute w σ)

theorem isometry_mem_symmetric {L d : ℕ} (v : OccupationSpace L d) :
    isometry L d v ∈ symmetricSubspace L d := by
  intro w σ
  simp only [isometry_apply, label_permute]

/-- Every symmetric tensor has occupation coordinates, with no dimension restriction. -/
theorem isometry_range (L d : ℕ) :
    (isometry L d).toLinearMap.range = symmetricSubspace L d := by
  classical
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact isometry_mem_symmetric u
  · intro hv
    let rep : Occupation L d → Word L d := fun q => (label_surjective L d q).choose
    have hrep : ∀ q, label (rep q) = q := fun q => (label_surjective L d q).choose_spec
    let coeff : OccupationSpace L d :=
      ⟨fun q => (Real.sqrt (multiplicity q : ℝ) : ℂ) * v (rep q),
        memℓp_gen (by simp only [ENNReal.toReal_ofNat]; exact (hasSum_fintype _).summable)⟩
    refine ⟨coeff, ?_⟩
    ext w
    change isometry L d coeff w = v w
    rw [isometry_apply]
    change ((Real.sqrt (multiplicity (label w) : ℝ) : ℂ) * v (rep (label w))) /
      (Real.sqrt (multiplicity (label w) : ℝ) : ℂ) = v w
    have hm : (Real.sqrt (multiplicity (label w) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos (label w))).ne'
    rw [mul_div_cancel_left₀ _ hm]
    exact (symmetric_iff_constant_on_fibers v).mp hv _ _ (hrep _)

end Cloning.GeneralSymmetricOccupation
