import Cloning.PhysicalCloningConverseSpectrum
import Cloning.TensorLANEmbeddingLocalSpectrum

/-! Uniformly admissible physical local spectra on every bounded score
window, including membership in an arbitrary interior spectral set. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.PhysicalCloningConverse
open Cloning.PCTLocalChart Cloning.PCTPhysicalFidelity Cloning.PCTPhysicalState
open Cloning.PCTUnitaryTransport Cloning.TensorLAN
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {k : ℕ}

/-- A total physical spectral chart. Its fallback is never used eventually
on a bounded trace-zero window. -/
def localSimpleSpectrum (p : SimpleSpectrum (k+1)) (h : Fin (k+1) → ℝ) (n : ℕ) :
    SimpleSpectrum (k+1) :=
  if hv : (∀ i, 0 < localSpectrum p.eigenvalue h n i) ∧
      StrictAnti (localSpectrum p.eigenvalue h n) ∧ (∑ i, localSpectrum p.eigenvalue h n i = 1)
  then ⟨localSpectrum p.eigenvalue h n, hv.1, hv.2.1, hv.2.2⟩
  else p

theorem eventually_localSimpleSpectrum_eigenvalue (p : SimpleSpectrum (k+1))
    (K : Set (Fin (k+1) → ℝ)) (hK : Bornology.IsBounded K)
    (hzero : ∀ h ∈ K, ∑ i, h i = 0) :
    ∀ᶠ n in atTop, ∀ h ∈ K,
      (localSimpleSpectrum p h n).eigenvalue = localSpectrum p.eigenvalue h n := by
  filter_upwards [eventually_localSpectrum_admissible p.eigenvalue p.positive p.strictAnti
    p.normalized K hK hzero] with n hn h hh
  simp only [localSimpleSpectrum, dif_pos (hn h hh)]

theorem localSpectrum_norm_sub (p h : Fin (k+1) → ℝ) (n : ℕ) :
    ‖localSpectrum p h n - p‖ = sampleScale n * ‖h‖ := by
  have he : localSpectrum p h n - p = sampleScale n • h := by
    funext i
    simp only [localSpectrum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_of_nonneg (by unfold sampleScale; positivity)]

/-- A bounded score window eventually stays in every neighborhood of its
base spectrum, with one sample threshold for the whole window. -/
theorem eventually_localSimpleSpectrum_mem (p : SimpleSpectrum (k+1))
    (K : Set (Fin (k+1) → ℝ)) (hK : Bornology.IsBounded K)
    (hzero : ∀ h ∈ K, ∑ i, h i = 0)
    (U : Set (SimpleSpectrum (k+1))) (hU : U ∈ 𝓝 p) :
    ∀ᶠ n in atTop, ∀ h ∈ K, localSimpleSpectrum p h n ∈ U := by
  rw [SimpleSpectrum.isEmbedding_eigenvalue.isInducing.nhds_eq_comap p] at hU
  obtain ⟨V,hV,hVU⟩ := hU
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨B,hB,hKB⟩ := hK.exists_pos_norm_le
  have ht : Tendsto (fun n => sampleScale n * B) atTop (𝓝 0) := by
    simpa only [zero_mul] using sampleScale_tendsto.mul_const B
  filter_upwards [eventually_localSimpleSpectrum_eigenvalue p K hK hzero,
    ht.eventually_lt_const hε] with n hn hsmall h hh
  apply hVU
  apply hεV
  rw [Metric.mem_ball, dist_eq_norm, hn h hh, localSpectrum_norm_sub]
  exact (mul_le_mul_of_nonneg_left (hKB h hh) (by unfold sampleScale; positivity)).trans_lt hsmall

/-- Interior base spectra remain in the given physical unknown-spectrum
parameter set under all bounded trace-zero local perturbations. -/
theorem eventually_localSimpleSpectrum_mem_of_interior
    (S : Set (SimpleSpectrum (k+1))) (p : SimpleSpectrum (k+1)) (hp : p ∈ interior S)
    (K : Set (Fin (k+1) → ℝ)) (hK : Bornology.IsBounded K)
    (hzero : ∀ h ∈ K, ∑ i, h i = 0) :
    ∀ᶠ n in atTop, ∀ h ∈ K, localSimpleSpectrum p h n ∈ S :=
  eventually_localSimpleSpectrum_mem p K hK hzero S (mem_interior_iff_mem_nhds.mp hp)

/-- The actual unitary orbit of the local spectrum is precisely the physical
LAN chart on the entire eventual admissible window. -/
theorem eventually_orbitState_localSimpleSpectrum (p : SimpleSpectrum (k+1))
    (K : Set (Parameters k)) (hK : IsCompact K)
    (hzero : ∀ θ ∈ K, ∑ i, θ.1 i = 0) :
    ∀ᶠ n in atTop, ∀ θ ∈ K,
      (TensorCloning.orbitState (localSimpleSpectrum p θ.1 n) (localUnitary p θ n)).matrix =
        chartMatrix p θ n := by
  have hK' : Bornology.IsBounded (Prod.fst '' K) := (hK.image continuous_fst).isBounded
  have hz : ∀ h ∈ Prod.fst '' K, ∑ i, h i = 0 := by
    rintro h ⟨θ,hθ,rfl⟩
    exact hzero θ hθ
  filter_upwards [eventually_localSimpleSpectrum_eigenvalue p (Prod.fst '' K) hK' hz]
    with n hn θ hθ
  change _ * _ * _ = _
  rw [localUnitary_star]
  have he := hn θ.1 ⟨θ,hθ,rfl⟩
  simp only [TensorCloning.orbitState, conjugatedState, diagonalState]
  rw [he]
  rfl

end Cloning.PhysicalCloningConverse
