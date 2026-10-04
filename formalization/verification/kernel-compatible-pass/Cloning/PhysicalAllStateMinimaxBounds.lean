import Cloning.PhysicalAllStateMinimaxLower
import Cloning.CloningValueComparisonInfimum

/-! The manuscript's unconditional all-density minimax bounds. The scalar
upper infimum is evaluated using the constructed sequence of simple spectra. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.PhysicalAllStateMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 150000

/-- The explicit all-state upper bound, with spectrum existence and the
infimum value discharged by genuine geometric probability spectra. -/
theorem limsup_value_le_upper (d : ℕ) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    limsup (fun n => value d n (m n)) atTop≤
      classicalValue γ (d+1)*γ^(-(((d+1:ℕ):ℝ)*(((d+1:ℕ):ℝ)-1))/4) := by
  letI : Nonempty (SimpleSpectrum (d+1)) :=
    ⟨Cloning.ValueComparison.geometricSequence (d+1) (by omega) 0⟩
  have hh := limsup_value_le_universal_infimum d m γ hγ hgain
  rw [Cloning.ValueComparison.universalValue_iInf (d+1) (by omega) hγ] at hh
  exact hh

/-- Both all-density bounds for every positive finite dimension and every
prescribed sequence of output counts with limiting gain γ>1. -/
theorem all_density_minimax_bounds (d : ℕ) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    γ^(-(((d+1:ℕ):ℝ)^2-1)/2)≤liminf (fun n => value d n (m n)) atTop ∧
    limsup (fun n => value d n (m n)) atTop≤
      classicalValue γ (d+1)*γ^(-(((d+1:ℕ):ℝ)*(((d+1:ℕ):ℝ)-1))/4) :=
  ⟨lower_le_liminf_value d m γ hγ hgain,limsup_value_le_upper d m γ hγ hgain⟩

end Cloning.PhysicalAllStateMinimax
