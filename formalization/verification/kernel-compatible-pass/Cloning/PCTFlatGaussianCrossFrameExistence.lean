import Cloning.PCTFlatGaussianCrossFrame
import Cloning.PCTTangentNormalization

/-! The Hermitian frame through a normalized Schmidt purification exists
without an assumed basis or a dimension premise beyond the physical register. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTFlatGaussianCross
open Cloning.PCT Cloning.PCTReducedGaussian
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Type*} [Fintype A] [DecidableEq A]

local instance flatCrossRegisterComplexFinite : FiniteDimensional ℂ (Register (A×A)) :=
  (registerBasis (A×A)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

local instance flatCrossRegisterRealFinite : FiniteDimensional ℝ (Register (A×A)) :=
  Module.Finite.trans ℂ (Register (A×A))

/-- The real Hermitian dimension equals the complex matrix dimension. -/
theorem hermitianSpace_finrank :
    Module.finrank ℝ (hermitianSpace A)=Fintype.card A^2 := by
  let b := stdOrthonormalBasis ℝ (hermitianSpace A)
  have h := Module.finrank_eq_card_basis (complexHermitianBasis b).toBasis
  simp only [Fintype.card_fin] at h
  rw [← h,Module.finrank_eq_card_basis (registerBasis (A×A)).toOrthonormalBasis.toBasis]
  simp [pow_two]

/-- A complex orthonormal frame of Hermitian coefficient matrices can be
chosen through every Hermitian unit vector. -/
theorem exists_hermitian_frame {s : ℕ} (hcard : Fintype.card A^2=s+1)
    (ψ : Register (A×A)) (hψ : ‖ψ‖=1) (hH : ∀ a b,star (ψ (b,a))=ψ (a,b)) :
    ∃ u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)),
      u 0=ψ ∧ ∀ i a b,star (u i (b,a))=u i (a,b) := by
  classical
  let x : hermitianSpace A := ⟨ψ,hH⟩
  let v : Fin (s+1) → hermitianSpace A := fun _ => x
  have hn : ‖x‖=1 := hψ
  have hc : Module.finrank ℝ (hermitianSpace A)=Fintype.card (Fin (s+1)) := by
    simpa only [Fintype.card_fin,hermitianSpace_finrank] using hcard
  have hv : Orthonormal ℝ (({0} : Set (Fin (s+1))).restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i=j := Subtype.ext (i.property.trans j.property.symm)
    simp only [hij,ite_true,Set.restrict_apply,v,real_inner_self_eq_norm_sq,hn,one_pow]
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hc
  refine ⟨complexHermitianBasis b,?_,?_⟩
  · rw [complexHermitianBasis_apply,hb 0 (Set.mem_singleton 0)]
  · intro i a c
    simpa only [complexHermitianBasis_apply] using (b i).property a c

/-- This applies in particular to the actual Schmidt coefficient vector. -/
theorem exists_hermitian_schmidt_frame {s : ℕ} (hcard : Fintype.card A^2=s+1)
    (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    ∃ u : OrthonormalBasis (Fin (s+1)) ℂ (Register (A×A)),
      u 0=coefficientVector (schmidtCoefficients p) ∧
      ∀ i a b,star (u i (b,a))=u i (a,b) := by
  apply exists_hermitian_frame hcard
  · have hh := schmidt_norm_sq p hp
    rw [hs] at hh
    nlinarith [norm_nonneg (coefficientVector (schmidtCoefficients p))]
  · intro a b
    by_cases hab : a=b
    · subst b
      simp [coefficientVector_apply,schmidtCoefficients]
    · simp [coefficientVector_apply,schmidtCoefficients,Matrix.diagonal_apply,hab,Ne.symm hab]

end Cloning.PCTFlatGaussianCross
