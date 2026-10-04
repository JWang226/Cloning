import Cloning.Main
import Mathlib.Tactic

/-! Ratio-wise flattening implies the usual ordered-spectrum majorization.
The conclusion is about every prefix sum of the actual normalized spectra. -/
noncomputable section
open scoped BigOperators
namespace Cloning.ValueComparison
set_option maxHeartbeats 800000

/-- Majorization for already decreasing, normalized spectra. -/
def SpectrumMajorizedBy {d : ℕ} (p' p : SimpleSpectrum d) : Prop :=
  ∀m : ℕ, (∑i : Fin d with i.val<m,p'.eigenvalue i)≤
    ∑i : Fin d with i.val<m,p.eigenvalue i

/-- Increasing every smaller-to-larger spectral ratio reduces every leading
partial sum. Total sums are already one in `SimpleSpectrum`. -/
theorem spectrumMajorizedBy_of_ratios {d : ℕ} (p p' : SimpleSpectrum d)
    (h : ∀ij : PairIndex d,p.ratio ij≤p'.ratio ij) : SpectrumMajorizedBy p' p := by
  classical
  intro m
  let S : Finset (Fin d) := Finset.univ.filter (fun i=>i.val<m)
  have hcross (i : Fin d) (hi : i∈S) (j : Fin d) (hj : j∈Sᶜ) :
      p.eigenvalue j*p'.eigenvalue i≤p'.eigenvalue j*p.eigenvalue i := by
    have hi' : i.val<m := (Finset.mem_filter.mp hi).2
    have hj' : ¬j.val<m := by simpa [S] using hj
    have hij : i<j := by simpa using (show i.val<j.val by omega)
    exact (div_le_div_iff₀ (p.positive i) (p'.positive i)).mp (h ⟨(i,j),hij⟩)
  have hx : (∑j∈Sᶜ,p.eigenvalue j)*(∑i∈S,p'.eigenvalue i)≤
      (∑j∈Sᶜ,p'.eigenvalue j)*(∑i∈S,p.eigenvalue i) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.sum_mul,Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj=>hcross i hi j hj)
  have hp : (∑i∈S,p.eigenvalue i)+(∑i∈Sᶜ,p.eigenvalue i)=1 := by
    rw [Finset.sum_add_sum_compl,p.normalized]
  have hp' : (∑i∈S,p'.eigenvalue i)+(∑i∈Sᶜ,p'.eigenvalue i)=1 := by
    rw [Finset.sum_add_sum_compl,p'.normalized]
  change (∑i∈S,p'.eigenvalue i)≤∑i∈S,p.eigenvalue i
  have hpC : (∑i∈Sᶜ,p.eigenvalue i)=1-∑i∈S,p.eigenvalue i := by linarith
  have hpC' : (∑i∈Sᶜ,p'.eigenvalue i)=1-∑i∈S,p'.eigenvalue i := by linarith
  rw [hpC,hpC'] at hx
  nlinarith

end Cloning.ValueComparison
