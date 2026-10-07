import Cloning.MatrixFidelityEmbedding
import Cloning.MatrixFidelityScaling
import Mathlib.Analysis.Matrix.Spectrum

/-! A dimension-explicit purity bound for the actual finite matrix root
fidelity against the maximally mixed state. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace Cloning.PCTPurity
open Cloning.MatrixFidelity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

lemma sqrt_polynomial_lower (t : ℝ) (ht : 0≤t) : 3*t-t^2≤2*Real.sqrt t := by
  have hs := Real.sqrt_nonneg t
  have hp := mul_nonneg (mul_nonneg hs (sq_nonneg (Real.sqrt t-1)))
    (by linarith : 0≤Real.sqrt t+2)
  have he := Real.sq_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt t)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem classical_purity_bound (p : ι→ℝ) (hp : ∀i,0≤p i) (hs : ∑i,p i=1) :
    1-(Cloning.BlockFidelity.classicalAffinity p (fun _ => (Fintype.card ι : ℝ)⁻¹))^2
      ≤ (Fintype.card ι : ℝ)*(∑i,(p i)^2)-1 := by
  let D : ℝ := Fintype.card ι
  have hD : 0<D := by
    change (0:ℝ)<(Fintype.card ι:ℝ)
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card ι)
  let F := Cloning.BlockFidelity.classicalAffinity p (fun _ => D⁻¹)
  have hpoint (i : ι) := sqrt_polynomial_lower (D*p i) (mul_nonneg hD.le (hp i))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hroot : ∑i,Real.sqrt (D*p i)=D*F := by
    simp only [Real.sqrt_mul hD.le,←Finset.mul_sum,F,Cloning.BlockFidelity.classicalAffinity,
      Real.sqrt_inv,←Finset.sum_mul]
    have hsd : Real.sqrt D≠0 := (Real.sqrt_pos.2 hD).ne'
    have hsq := Real.sq_sqrt hD.le
    field_simp
    rw [hsq]
    ring
  have he : (∑i,(3*(D*p i)-(D*p i)^2))=3*D-D^2*(∑i,(p i)^2) := by
    simp_rw [mul_pow]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum,hs]
    ring
  rw [he,←Finset.mul_sum,hroot] at hsum
  have hb : 3-D*(∑i,(p i)^2)≤2*F := by nlinarith
  change 1-F^2≤D*(∑i,(p i)^2)-1
  nlinarith [sq_nonneg (F-1)]

/-- The actual normalized identity matrix. -/
def maximallyMixed : Matrix ι ι ℂ := (Fintype.card ι : ℝ)⁻¹ • (1 : Matrix ι ι ℂ)

theorem maximallyMixed_diagonal : maximallyMixed (ι := ι)=
    Matrix.diagonal (fun _ => ((Fintype.card ι : ℝ)⁻¹ : ℂ)) := by
  ext i j
  simp [maximallyMixed,Matrix.one_apply,Matrix.diagonal_apply]

theorem fidelity_purity_bound (ρ : State ι) :
    1-(fidelity ρ.matrix (maximallyMixed (ι := ι)))^2 ≤
      (Fintype.card ι : ℝ)*(Matrix.trace (ρ.matrix*ρ.matrix)).re-1 := by
  let p : ι→ℝ := ρ.positive.isHermitian.eigenvalues
  let U : Matrix ι ι ℂ := ρ.positive.isHermitian.eigenvectorUnitary
  let P : Matrix ι ι ℂ := Matrix.diagonal (fun i => (p i : ℂ))
  have hp : ∀i,0≤p i := ρ.positive.eigenvalues_nonneg
  have hs : ∑i,p i=1 := by
    have h := congrArg Complex.re ρ.positive.isHermitian.trace_eq_sum_eigenvalues
    rw [ρ.trace_one] at h
    simpa only [Complex.one_re,Complex.re_sum,Complex.ofReal_re] using h.symm
  have hU : Uᴴ*U=1 := Unitary.star_mul_self_of_mem ρ.positive.isHermitian.eigenvectorUnitary.property
  have hU' : U*Uᴴ=1 := Unitary.mul_star_self_of_mem ρ.positive.isHermitian.eigenvectorUnitary.property
  have hρ : ρ.matrix=U*P*Uᴴ := ρ.positive.isHermitian.spectral_theorem
  have hP : P.PosSemidef := Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr ⟨hp i,rfl⟩)
  have hM : (maximallyMixed (ι := ι)).PosSemidef := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hUM : U*maximallyMixed*Uᴴ=maximallyMixed (ι := ι) := by
    simp only [maximallyMixed,mul_smul_comm,smul_mul_assoc,Matrix.mul_one,hU']
  have hF : fidelity ρ.matrix maximallyMixed=Cloning.BlockFidelity.classicalAffinity p
      (fun _ => (Fintype.card ι : ℝ)⁻¹) := by
    rw [hρ,←hUM,fidelity_unitary_conjugation U hU hP hM,maximallyMixed_diagonal]
    change fidelity (Matrix.diagonal (fun i => (p i : ℂ)))
      (Matrix.diagonal (fun _ : ι => ((Fintype.card ι : ℝ)⁻¹ : ℂ))) = _
    simpa only [Complex.ofReal_inv] using
      fidelity_diagonal_real p (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) hp
        (fun _ => inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card ι)))
  have ht : (Matrix.trace (ρ.matrix*ρ.matrix)).re=∑i,(p i)^2 := by
    have he : ρ.matrix*ρ.matrix=U*(P*P)*Uᴴ := by
      rw [hρ]
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc Uᴴ,hU,Matrix.one_mul]
    rw [he,Matrix.trace_mul_comm,←Matrix.mul_assoc,hU,Matrix.one_mul]
    simp only [P,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum,
      ←Complex.ofReal_mul,Complex.ofReal_re,pow_two]
  rw [hF,ht]
  exact classical_purity_bound p hp hs

end Cloning.PCTPurity
