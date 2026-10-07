import Cloning.TensorGibbsPartitionLimit
import Cloning.YoungUniformLocalPhysicalMass
import Cloning.YoungCompatibility

/-! Physical character normalization along central lattice sequences.
All diverging root-gap conditions are derived from the strict limiting
spectrum; eventual partition constraints suffice. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungMultinomial
open Cloning.TensorLie Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The exact physical character normalized by its highest eigenvalue has the
required limit. There is no representation or character-normalization premise. -/
theorem physicalSectorCharacter_div_highest_tendsto {d : ℕ}
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (μ : ℕ → Fin d → ℕ)
    (hμ : ∀ᶠ k in atTop, Antitone (μ k))
    (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hord : StrictAnti p)
    (hlim : ∀ i, Tendsto (fun k ↦ pN k i) atTop (𝓝 (p i)))
    (hcount : ∀ i, Tendsto (fun k ↦ (μ k i : ℝ) / (n k : ℝ)) atTop (𝓝 (p i))) :
    Tendsto (fun k ↦ physicalSectorCharacter (μ k) (pN k) /
      (∏ i, pN k i ^ μ k i)) atTop (𝓝 (spectralCorrection p)⁻¹) := by
  let ν : ℕ → Fin d → ℕ := fun k ↦ if Antitone (μ k) then μ k else fun _ ↦ 0
  have hν : ∀ k, Antitone (ν k) := by
    intro k
    dsimp [ν]
    split_ifs with h
    · exact h
    · intro i j _; rfl
  have heq : ∀ᶠ k in atTop, ν k = μ k := hμ.mono fun k hk ↦ by simp [ν, hk]
  have hνlim i : Tendsto (fun k ↦ (ν k i : ℝ) / (n k : ℝ)) atTop (𝓝 (p i)) := by
    apply (hcount i).congr'
    filter_upwards [heq] with k hk
    rw [hk]
  obtain ⟨a, ha, _, hagap0⟩ := YoungCompatibility.compact_spectra_positive_gap
    ({p} : Set (Fin d → ℝ)) isCompact_singleton
    (by intro q hq; have he : q = p := Set.mem_singleton_iff.mp hq; simpa [he] using hp)
    (by intro q hq; have he : q = p := Set.mem_singleton_iff.mp hq; simpa [he] using hord)
  have hagap (r : PositiveRoot d) : a ≤ p r.val.1 - p r.val.2 :=
    hagap0 p (by simp) r.val.1 r.val.2 r.property
  let δ := fun k ↦ (a / 2) * (n k : ℝ)
  have hδ : Tendsto δ atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hn).const_mul_atTop (by positivity : (0 : ℝ) < a / 2)
  have hscaled : ∀ᶠ k in atTop, ∀ r : PositiveRoot d,
      a / 2 ≤ (ν k r.val.1 : ℝ) / (n k : ℝ) - (ν k r.val.2 : ℝ) / (n k : ℝ) := by
    apply eventually_all.mpr
    intro r
    have hh := (hνlim r.val.1).sub (hνlim r.val.2)
    exact (hh.eventually (eventually_gt_nhds (show a / 2 < p r.val.1 - p r.val.2 by
      linarith [hagap r]))).mono (fun _ h ↦ h.le)
  have hgap : ∀ᶠ k in atTop, ∀ r : PositiveRoot d,
      δ k ≤ (ν k r.val.1 : ℝ) - ν k r.val.2 := by
    filter_upwards [hscaled, hn.eventually (eventually_gt_atTop 0)] with k hk hnK r
    have hnk : (0 : ℝ) < n k := by exact_mod_cast hnK
    have hh := hk r
    rw [← sub_div, le_div_iff₀ hnk] at hh
    exact hh
  have ht := sectorPartitionFunction_div_highest_tendsto ν hν δ hδ hgap pN p hp hord hlim
  simp only [rootBoltzmann, root_partition_product_eq_spectralCorrection_inv] at ht
  have ht' : Tendsto (fun k ↦ physicalSectorCharacter (ν k) (pN k) /
      (∏ i, pN k i ^ ν k i)) atTop (𝓝 (spectralCorrection p)⁻¹) := by
    convert ht using 1
    funext k
    simp only [physicalSectorCharacter, dif_pos (hν k)]
  apply ht'.congr'
  filter_upwards [heq] with k hk
  rw [hk]



theorem spectralCorrection_pos {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hord : StrictAnti p) : 0 < spectralCorrection p := by
  unfold spectralCorrection
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr ((div_lt_one (hp i)).mpr (hord (Finset.mem_Ioi.mp hj)))

end Cloning.YoungMultinomial
