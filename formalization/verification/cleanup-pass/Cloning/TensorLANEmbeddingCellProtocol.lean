import Cloning.TensorLANEmbeddingWhiteningGaussian
import Cloning.TensorLANEmbeddingSelector

/-! Parameter-independent classical cells and quantization, coupled to the
actual physical Schur/Fock channels at every sample size. -/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace NNReal ENNReal
open MeasureTheory Filter
namespace Cloning.TensorLAN
open Cloning.YoungHyperplane Cloning.PCTJointGaussianWhitening Cloning.TensorLie
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.PCT
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

/-- The genuine uniform cell probability density on the full root space. -/
def rootCellDensity (d N : ℕ) (p : Fin (d+1) → ℝ) (mu : Lattice d (N : ℤ)) :
    rootSpace d → ℝ :=
  sampleInterpolate d N p (fun nu => (PMF.pure mu nu).toReal)

theorem rootCellDensity_nonneg (d N : ℕ) (p : Fin (d+1) → ℝ)
    (mu : Lattice d (N : ℤ)) (x : rootSpace d) : 0 ≤ rootCellDensity d N p mu x := by
  unfold rootCellDensity sampleInterpolate euclideanInterpolate interpolate
    YoungRounding.affineDensity YoungRounding.interpolate
  positivity

theorem rootCellDensity_integral (d N : ℕ) (hN : 0 < N) (p : Fin (d+1) → ℝ)
    (mu : Lattice d (N : ℤ)) : (∫ x, rootCellDensity d N p mu x) = 1 := by
  rw [rootCellDensity, sampleInterpolate_integral d N (by exact_mod_cast hN)]
  · exact (YoungCompatibility.hasSum_probability (PMF.pure mu)).tsum_eq
  · exact (YoungCompatibility.hasSum_probability (PMF.pure mu)).summable

theorem rootCellDensity_integrable (d N : ℕ) (hN : 0 < N) (p : Fin (d+1) → ℝ)
    (mu : Lattice d (N : ℤ)) : Integrable (rootCellDensity d N p mu) := by
  by_contra hi
  have h := rootCellDensity_integral d N hN p mu
  rw [integral_undef hi] at h
  norm_num at h

/-- Each physical copy has its actual complete affine lattice label. -/
def schurCopyLattice (N d : ℕ) (i : SchurCopy N (d+1)) : Lattice d (N : ℤ) :=
  ⟨fun a => (((recursivePhysicalDecomposition N (d+1)).get i).weight a : ℤ),
    by
      change (∑ a, (((recursivePhysicalDecomposition N (d+1)).get i).weight a : ℤ)) = (N : ℤ)
      exact_mod_cast ((recursivePhysicalDecomposition N (d+1)).get i).weight_sum⟩

variable (p : Fin (d+1) → ℝ) (hp : ∀ a, 0 < p a)
    (b : OrthonormalBasis (Fin (d+1)) ℝ (EuclideanSpace ℝ (Fin (d+1))))
    (hb : b 0 = sqrtSpectrum p)

/-- At positive sample sizes this is precisely the whitened fixed-reference
cell. The zero-fold experiment is completed by a normalized Gaussian. -/
def physicalCellDensity (N : ℕ) (i : SchurCopy N (d+1)) : (Fin d → ℝ) → ℝ :=
  if 0 < N then whiteningDensity (rootWhitening p hp b hb)
    (rootCellDensity d N p (schurCopyLattice N d i))
  else GaussianAffinity.productDensity (fun _ : Fin d => (1/2 : ℝ))

theorem physicalCellDensity_nonneg (N : ℕ) (i : SchurCopy N (d+1)) (x : Fin d → ℝ) :
    0 ≤ physicalCellDensity p hp b hb N i x := by
  unfold physicalCellDensity
  split_ifs
  · exact mul_nonneg (NNReal.coe_nonneg _) (rootCellDensity_nonneg ..)
  · exact GaussianAffinity.productDensity_nonneg _ _

theorem physicalCellDensity_integrable (N : ℕ) (i : SchurCopy N (d+1)) :
    Integrable (physicalCellDensity p hp b hb N i) := by
  unfold physicalCellDensity
  split_ifs with hn
  · exact whiteningDensity_integrable _ _ (rootCellDensity_integrable d N hn p _)
  · exact Integrable.fintype_prod fun _ => GaussianAffinity.integrable_density (by norm_num)

theorem physicalCellDensity_integral (N : ℕ) (i : SchurCopy N (d+1)) :
    (∫ x, physicalCellDensity p hp b hb N i x) = 1 := by
  unfold physicalCellDensity
  split_ifs with hn
  · rw [whiteningDensity_integral, rootCellDensity_integral d N hn]
  · exact GaussianAffinity.integral_productDensity _ (fun _ => by norm_num)

/-- A literal forward channel, depending only on the fixed base spectrum,
its whitening frame, and the retained quantum cutoff. -/
def physicalCellForward (N R : ℕ) :
    QuantumToHybrid (TensorRegister N (Fin (d+1))) (RootFock (d+1))
      (volume : Measure (Fin d → ℝ)) :=
  schurForward N (d+1) R (physicalCellDensity p hp b hb N)
    (physicalCellDensity_integrable p hp b hb N)
    (physicalCellDensity_nonneg p hp b hb N)
    (physicalCellDensity_integral p hp b hb N)

def physicalCellQuantizer (N : ℕ) (x : Fin d → ℝ) : Lattice d (N : ℤ) :=
  sampleLabel d N p ((rootWhitening p hp b hb).symm x)

theorem physicalCellQuantizer_measurable (N : ℕ) :
    Measurable (physicalCellQuantizer p hp b hb N) :=
  (measurable_sampleLabel d N p).comp (rootWhitening p hp b hb).symm.continuous.measurable

/-- A fixed actual tensor vector provides the completely positive replacement
on any unrepresented affine lattice outcome. -/
def physicalFallback (N d : ℕ) : DensityState (TensorRegister N (Fin (d+1))) :=
  DensityState.pure (registerBasis (Fin N → Fin (d+1)) (fun _ => 0))
    ((registerBasis _).orthonormal.norm_eq_one _)

/-- Reverse quantization reads a complete integer label, chooses uniformly
among its physical copies, and uses the genuine all-input reverse sector map. -/
def physicalCellReverse (N R : ℕ) :
    HybridToQuantum (RootFock (d+1)) (TensorRegister N (Fin (d+1)))
      (volume : Measure (Fin d → ℝ)) :=
  schurReverse N (d+1) R (physicalFallback N d)
    (uniformLabelSelector (schurCopyLattice N d) (physicalCellQuantizer p hp b hb N))
    (fun i => (uniformLabelSelector_measurable _ _
      (physicalCellQuantizer_measurable p hp b hb N) i).aestronglyMeasurable)
    (uniformLabelSelector_nonneg _ _) (uniformLabelSelector_sum _ _)

end Cloning.TensorLAN
