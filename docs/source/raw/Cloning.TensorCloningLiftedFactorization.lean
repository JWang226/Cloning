import Cloning.TensorCloningShrinkingMixture
import Cloning.TensorCloningUniformBlocks
import Cloning.TensorCloningUniformCovariance

/-! Literal uniform factorization of arbitrary lifted physical transition
kernels whose joint label laws concentrate in arbitrary shrinking windows. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Classical Matrix Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

def copyShrinkingWindow (n d : ℕ) (p : Fin d → ℝ) (δ : ℝ) (i : SchurCopy n d) : Prop :=
  ∀ a,|((((recursivePhysicalDecomposition n d).get i).weight a : ℝ)/(n : ℝ))-p a|≤δ

def kernelJointWeight (n m d : ℕ) (p : Fin d → ℝ)
    (q : SchurCopy n d → SchurCopy m d → ℝ) (i : SchurCopy n d) (j : SchurCopy m d) : ℝ :=
  knownCopyWeight n d p i*q i j

def kernelBadMass (n m d : ℕ) (p : Fin d → ℝ) (δ : ℝ)
    (q : SchurCopy n d → SchurCopy m d → ℝ) : ℝ :=
  ∑ j,∑ i,if copyShrinkingWindow n d p δ i ∧ copyShrinkingWindow m d p δ j
    then 0 else kernelJointWeight n m d p q i j

def kernelAffinity (n m d : ℕ) (p : Fin d → ℝ)
    (q : SchurCopy n d → SchurCopy m d → ℝ) : ℝ :=
  Cloning.BlockFidelity.classicalAffinity (fun j => ∑ i,kernelJointWeight n m d p q i j)
    (knownCopyWeight m d p)

theorem kernelJointWeight_nonneg (n m d : ℕ) (p : Fin d → ℝ)
    (q : SchurCopy n d → SchurCopy m d → ℝ) (hq : ∀ i j,0≤q i j) :
    ∀ i j,0≤kernelJointWeight n m d p q i j :=
  fun i j => mul_nonneg (knownCopyWeight_nonneg n d p i) (hq i j)

theorem kernelJointWeight_sum (n m d : ℕ) (p : Fin d → ℝ)
    (hp : ∀ a,0≤p a) (hspec : ∑ a,p a=1)
    (q : SchurCopy n d → SchurCopy m d → ℝ) (hs : ∀ i,∑ j,q i j=1) :
    (∑ j,∑ i,kernelJointWeight n m d p q i j)=1 := by
  rw [Finset.sum_comm]
  simp only [kernelJointWeight,← Finset.mul_sum,hs,mul_one]
  exact knownCopyWeight_sum n d p hp hspec

theorem kernelBadMass_nonneg (n m d : ℕ) (p : Fin d → ℝ) (δ : ℝ)
    (q : SchurCopy n d → SchurCopy m d → ℝ) (hq : ∀ i j,0≤q i j) :
    0≤kernelBadMass n m d p δ q := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact kernelJointWeight_nonneg n m d p q hq i j

/-- The joint-mixture action is derived for every actual stochastic table. -/
theorem channel_rotated_apply (n m d : ℕ) (p : Fin d → ℝ) (hp : ∀ a,0<p a)
    (q : SchurCopy n d → SchurCopy m d → ℝ) (hq : ∀ i j,0≤q i j) (hs : ∀ i,∑ j,q i j=1)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (channel n m d q hq hs).toLinearMap
      (matrixTensorPower (U*Matrix.diagonal (fun a => (p a : ℂ))*Uᴴ) n)=
      ∑ ij : SchurCopy n d × SchurCopy m d,(kernelJointWeight n m d p q ij.1 ij.2 : ℂ) •
        (copyTransition n m d ij.1 ij.2).toLinearMap
          (canonicalRotatedGibbs ((recursivePhysicalDecomposition n d).get ij.1) U p) := by
  rw [channel_apply]
  simp only [matrixTensorPower_canonical_block,canonicalTensorWeight_rotated_diagonal _ U p hp,
    map_smul,Fintype.sum_prod_type,kernelJointWeight,Complex.ofReal_mul,mul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- A uniform quantitative bound for arbitrary lifted kernels. The genuine
sector-fidelity error is discharged, leaving only their literal discarded mass. -/
theorem eventually_uniform_kernel_factorization_bound
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (η : ℝ) (hη : 0<η) :
    ∀ᶠ (n : ℕ) in atTop,∀ p∈K,
      ∀ (q : SchurCopy n (d+1) → SchurCopy (m n) (d+1) → ℝ)
        (hq : ∀ i j,0≤q i j) (hs : ∀ i,∑ j,q i j=1),
      ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (channel n (m n) (d+1) q hq hs) p U-
        orbitalValue γ p*kernelAffinity n (m n) (d+1) p.eigenvalue q|≤
      η+2*Real.sqrt (kernelBadMass n (m n) (d+1) p.eigenvalue (δ n) q) := by
  filter_upwards [eventually_uniform_shrinkingWindow_mixture_fidelity_fintype K hK m γ hγ hgain δ hδ η hη]
    with n hn p hp q hq hs U
  rw [spectrumPayoff_unitary_of_covariant n (m n) _ p U
    (channel_covariant n (m n) (d+1) q hq hs U (Unitary.star_mul_self_of_mem U.property))]
  let w := kernelJointWeight n (m n) (d+1) p.eigenvalue q
  have hw := kernelJointWeight_nonneg n (m n) (d+1) p.eigenvalue q hq
  let keep := fun i j => copyShrinkingWindow n (d+1) p.eigenvalue (δ n) i ∧
    copyShrinkingWindow (m n) (d+1) p.eigenvalue (δ n) j
  have hkeep : ∀ i j,keep i j ↔ copyShrinkingWindow n (d+1) p.eigenvalue (δ n) i ∧
      copyShrinkingWindow (m n) (d+1) p.eigenvalue (δ n) j := fun _ _ => Iff.rfl
  clear_value keep
  have htotal := kernelJointWeight_sum n (m n) (d+1) p.eigenvalue
    (fun a => (p.positive a).le) p.normalized q hs
  have hf := copyBlocks_factorization_bound n (m n) p 1 w hw htotal.le keep
    (orbitalValue γ p) η (orbitalValue_pos hγ p).le (orbitalValue_le_one hγ p) hη.le (by
      intro j hr
      have hj : copyShrinkingWindow (m n) (d+1) p.eigenvalue (δ n) j := by
        by_contra hh
        simp only [retainedCopyWeight,PositiveTraceClass.maskedWeight,hkeep,hh,and_false,
          if_false,Finset.sum_const_zero] at hr
        exact lt_irrefl 0 hr
      rw [retainedCopyWeight_sum] at hr
      simp only [OneMemClass.coe_one]
      rw [normalizedCopyBlock_rootFidelity_one n (m n) (d+1) p.eigenvalue p.positive w hw keep j hr]
      exact (hn p hp {i : SchurCopy n (d+1) // keep i j}
        (fun i => ((recursivePhysicalDecomposition n (d+1)).get i.val).weight)
        ((recursivePhysicalDecomposition (m n) (d+1)).get j).weight
        (fun i => ((recursivePhysicalDecomposition n (d+1)).get i.val).weight_antitone)
        ((recursivePhysicalDecomposition (m n) (d+1)).get j).weight_antitone
        (fun i => ((hkeep i.val j).mp i.property).1) hj
        (fun i => w i.val j/∑ a : {i // keep i j},w a.val j)
        (fun i => div_nonneg (hw i.val j) hr.le)
        (retainedCopyProbability_sum n (m n) (d+1) w keep j hr)).le)
  have he := spectrumPayoff_eq_copyBlocks n (m n) (channel n (m n) (d+1) q hq hs) p 1 w hw
    (channel_rotated_apply n (m n) (d+1) p.eigenvalue p.positive q hq hs 1)
  rw [← he] at hf
  simpa only [kernelAffinity,kernelBadMass,hkeep] using hf

/-- The manuscript's factorization lemma for arbitrary (possibly
spectrum-dependent) actual lifted channels. The only extra asymptotic premise
is the stated uniform vanishing of bad joint-label probability. -/
theorem eventually_uniform_lifted_fidelity_factorization
    (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (q : ∀ n,SimpleSpectrum (d+1) → SchurCopy n (d+1) → SchurCopy (m n) (d+1) → ℝ)
    (hq : ∀ n p i j,0≤q n p i j) (hs : ∀ n p i,∑ j,q n p i j=1)
    (hbad : ∀ η : ℝ,0<η → ∀ᶠ n in atTop,∀ p∈K,
      kernelBadMass n (m n) (d+1) p.eigenvalue (δ n) (q n p)<η)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ p∈K,∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (channel n (m n) (d+1) (q n p) (hq n p) (hs n p)) p U-
        orbitalValue γ p*kernelAffinity n (m n) (d+1) p.eigenvalue (q n p)|<ε := by
  filter_upwards [eventually_uniform_kernel_factorization_bound K hK m γ hγ hgain δ hδ (ε/2) (by positivity),
    hbad ((ε/4)^2) (by positivity)] with n hn hb p hp U
  have hh := hn p hp (q n p) (hq n p) (hs n p) U
  have hz := kernelBadMass_nonneg n (m n) (d+1) p.eigenvalue (δ n) (q n p) (hq n p)
  have hsmall := hb p hp
  have hsq := Real.sq_sqrt hz
  have hnonneg := Real.sqrt_nonneg (kernelBadMass n (m n) (d+1) p.eigenvalue (δ n) (q n p))
  have hroot : Real.sqrt (kernelBadMass n (m n) (d+1) p.eigenvalue (δ n) (q n p))<ε/4 := by nlinarith
  linarith

end Cloning.TensorCloning
