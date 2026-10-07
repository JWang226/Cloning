import Cloning.TensorGibbsWeights
import Mathlib.Analysis.SpecificLimits.Normed

/-! Uniform summable height envelopes derived from a strictly ordered positive
spectrum. The same envelope works eventually for any moving spectrum converging
to it, which is the form needed for physical central windows. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem rootBoltzmann_lt_one (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) (r : PositiveRoot d) : rootBoltzmann p r < 1 :=
  (div_lt_one (hp _)).mpr (hord r.property)

/-- A common exponential rate is obtained from the finitely many physical
root ratios; the height envelope is not assumed. -/
theorem exists_root_height_decay (p : Fin d → ℝ) (hp : ∀ a, 0 < p a)
    (hord : StrictAnti p) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ r : PositiveRoot d,
      rootBoltzmann p r < θ ^ r.height := by
  let t : ℕ → ℝ := fun N => 1 - 1 / ((N : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr (r : PositiveRoot d) : ∀ᶠ N : ℕ in atTop, rootBoltzmann p r < t N ^ r.height :=
    (ht.pow r.height).eventually (eventually_gt_nhds (by
      simpa only [one_pow] using rootBoltzmann_lt_one p hp hord r))
  have hall : ∀ᶠ N : ℕ in atTop, ∀ r : PositiveRoot d, rootBoltzmann p r < t N ^ r.height :=
    Filter.eventually_all.mpr hr
  obtain ⟨N, hN, hNr⟩ := ((eventually_ge_atTop 1).and hall).exists
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
  have hlt : 1 / ((N : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  exact ⟨t N, by dsimp [t]; linarith, by dsimp [t]; linarith, hNr⟩

theorem rootBoltzmann_tendsto (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a)))
    (r : PositiveRoot d) :
    Tendsto (fun N => rootBoltzmann (pN N) r) atTop (𝓝 (rootBoltzmann p r)) :=
  (hlim _).div (hlim _) (hp _).ne'

/-- Moving spectra inherit one height envelope from their strict limit. -/
theorem exists_eventual_root_height_decay (pN : ℕ → Fin d → ℝ) (p : Fin d → ℝ)
    (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hlim : ∀ a, Tendsto (fun N => pN N a) atTop (𝓝 (p a))) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (∀ r : PositiveRoot d, rootBoltzmann p r ≤ θ ^ r.height) ∧
      ∀ᶠ N : ℕ in atTop, ∀ r : PositiveRoot d, rootBoltzmann (pN N) r ≤ θ ^ r.height := by
  obtain ⟨θ, hθ, hθ1, hr⟩ := exists_root_height_decay p hp hord
  refine ⟨θ, hθ, hθ1, fun r => (hr r).le, Filter.eventually_all.mpr ?_⟩
  intro r
  exact ((rootBoltzmann_tendsto pN p hp hlim r).eventually (eventually_lt_nhds (hr r))).mono
    (fun N h => h.le)

def heightEnvelope (d : ℕ) (θ : ℝ) (H : ℕ) : ℝ :=
  ((H+1 : ℕ) : ℝ)^Fintype.card (PositiveRoot d) * θ^H

theorem heightEnvelope_summable (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    Summable (heightEnvelope d θ) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one
    (Fintype.card (PositiveRoot d)) (r := θ) (by simpa [abs_of_pos hθ] using hθ1)
  have ht := (summable_nat_add_iff 1).mpr hs
  have hm := ht.mul_right θ⁻¹
  convert hm using 1
  funext H
  simp only [heightEnvelope, pow_succ, mul_assoc, mul_inv_cancel₀ hθ.ne', mul_one]

end Cloning.TensorLie
