import Cloning.TensorCloningAchievabilityProbability
import Cloning.YoungCompatibility

/-! Typical independent source and target labels force actual Cartan
compatibility and the required diverging gaps and gain fractions. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {d : ℕ}

/-- Strict positive limiting coordinate differences force an actual natural
partition difference; compatibility is a conclusion. -/
theorem eventually_partitionCompatible_of_scaled_limits
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (μ ν : ℕ → Fin d → ℕ)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (γ : ℝ) (hγ : 1 < γ)
    (hμ : ∀ a, Tendsto (fun k => (μ k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a)))
    (hν : ∀ a, Tendsto (fun k => (ν k a : ℝ)/(n k : ℝ)) atTop (𝓝 (γ*p a))) :
    ∀ᶠ k in atTop, PartitionCompatible (μ k) (ν k) := by
  have hd (a : Fin d) : Tendsto
      (fun k => (ν k a : ℝ)/(n k : ℝ)-(μ k a : ℝ)/(n k : ℝ)) atTop (𝓝 ((γ-1)*p a)) := by
    convert (hν a).sub (hμ a) using 1 <;> ring
  have hpos : ∀ᶠ k in atTop, ∀ a,
      0 < (ν k a : ℝ)/(n k : ℝ)-(μ k a : ℝ)/(n k : ℝ) :=
    eventually_all.mpr (fun a => (hd a).eventually (eventually_gt_nhds (mul_pos (sub_pos.mpr hγ) (hp a))))
  have hgap : ∀ᶠ k in atTop, ∀ r : PositiveRoot d,
      0 < ((ν k r.val.1 : ℝ)/(n k : ℝ)-(μ k r.val.1 : ℝ)/(n k : ℝ)) -
        ((ν k r.val.2 : ℝ)/(n k : ℝ)-(μ k r.val.2 : ℝ)/(n k : ℝ)) := by
    apply eventually_all.mpr
    intro r
    apply ((hd r.val.1).sub (hd r.val.2)).eventually
    apply eventually_gt_nhds
    nlinarith [hord r.property]
  filter_upwards [hpos, hgap, hn.eventually (eventually_gt_atTop 0)] with k hk hg hnk
  have hnreal : (0 : ℝ) < n k := by exact_mod_cast hnk
  have hle (a : Fin d) : μ k a ≤ ν k a := by
    have hh := hk a
    rw [← sub_div, div_pos_iff_of_pos_right hnreal] at hh
    exact_mod_cast (sub_pos.mp hh).le
  refine ⟨hle, ?_⟩
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  have hh := hg ⟨(a,b),hab⟩
  simp only at hh
  rw [← sub_div, ← sub_div, ← sub_div, div_pos_iff_of_pos_right hnreal] at hh
  have hreal : ((ν k b-μ k b : ℕ) : ℝ) ≤ ((ν k a-μ k a : ℕ) : ℝ) := by
    rw [Nat.cast_sub (hle a), Nat.cast_sub (hle b)]
    linarith
  exact_mod_cast hreal

theorem difference_scaled_tendsto
    (n : ℕ → ℕ) (μ ν : ℕ → Fin d → ℕ) (p : Fin d → ℝ) (γ : ℝ)
    (hμ : ∀ a, Tendsto (fun k => (μ k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a)))
    (hν : ∀ a, Tendsto (fun k => (ν k a : ℝ)/(n k : ℝ)) atTop (𝓝 (γ*p a)))
    (hc : ∀ᶠ k in atTop, PartitionCompatible (μ k) (ν k)) (a : Fin d) :
    Tendsto (fun k => ((ν k a-μ k a : ℕ) : ℝ)/(n k : ℝ)) atTop (𝓝 ((γ-1)*p a)) := by
  have hh := (hν a).sub (hμ a)
  have he : γ*p a-p a = (γ-1)*p a := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hc] with k hk
  rw [Nat.cast_sub (hk.1 a), sub_div]

/-- Common diverging physical root-gap bounds follow from actual row
frequencies. The limiting vector need not have total mass one. -/
theorem exists_root_gap_of_scaled_limits
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (μ : ℕ → Fin d → ℕ)
    (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (hμ : ∀ a, Tendsto (fun k => (μ k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a))) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop atTop ∧
      ∀ᶠ k in atTop, ∀ r : PositiveRoot d, δ k ≤ rootGap (μ k) r := by
  obtain ⟨a,ha,_,hag⟩ := YoungCompatibility.compact_spectra_positive_gap
    ({p} : Set (Fin d → ℝ)) isCompact_singleton
    (by intro q hq; simpa only [Set.mem_singleton_iff.mp hq] using hp)
    (by intro q hq; simpa only [Set.mem_singleton_iff.mp hq] using hord)
  refine ⟨fun k => (a/2)*(n k : ℝ),
    (tendsto_natCast_atTop_atTop.comp hn).const_mul_atTop (by positivity), ?_⟩
  have hscaled : ∀ᶠ k in atTop, ∀ r : PositiveRoot d,
      a/2 ≤ (μ k r.val.1 : ℝ)/(n k : ℝ)-(μ k r.val.2 : ℝ)/(n k : ℝ) := by
    apply eventually_all.mpr
    intro r
    have hb := hag p (by simp) r.val.1 r.val.2 r.property
    exact (((hμ r.val.1).sub (hμ r.val.2)).eventually
      (eventually_gt_nhds (by linarith))).mono (fun _ h => h.le)
  filter_upwards [hscaled, hn.eventually (eventually_gt_atTop 0)] with k hk hnk r
  have hnreal : (0 : ℝ) < n k := by exact_mod_cast hnk
  have hh := hk r
  rw [← sub_div, le_div_iff₀ hnreal] at hh
  exact hh

/-- Independent typical source and target labels have the appropriate
frequencies relative to the common input scale. -/
theorem typical_pair_scaled_limits
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (μ ν : ℕ → Fin d → ℕ) (p : Fin d → ℝ) (γ : ℝ)
    (hγ : Tendsto (fun k => (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (hμ : ∀ᶠ k in atTop, TypicalLabel (n k) p (μ k))
    (hν : ∀ᶠ k in atTop, TypicalLabel (m k) p (ν k)) :
    (∀ a, Tendsto (fun k => (μ k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a))) ∧
    (∀ a, Tendsto (fun k => (ν k a : ℝ)/(n k : ℝ)) atTop (𝓝 (γ*p a))) := by
  refine ⟨fun a => typicalLabel_ratio_tendsto n hn μ (fun _ => p) p (fun _ => tendsto_const_nhds) hμ a, ?_⟩
  intro a
  have hh := hγ.mul (typicalLabel_ratio_tendsto m hm ν (fun _ => p) p (fun _ => tendsto_const_nhds) hν a)
  apply hh.congr'
  filter_upwards [hm.eventually (eventually_gt_atTop 0)] with k hmk
  have hmreal : (m k : ℝ) ≠ 0 := by exact_mod_cast hmk.ne'
  field_simp

/-- The root-wise Cartan fraction tends to the inverse physical cloning gain. -/
theorem rootFraction_difference_tendsto
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (μ ν : ℕ → Fin d → ℕ)
    (p : Fin d → ℝ) (hord : StrictAnti p) (γ : ℝ) (hγ : 0 < γ)
    (hμ : ∀ a, Tendsto (fun k => (μ k a : ℝ)/(n k : ℝ)) atTop (𝓝 (p a)))
    (hν : ∀ a, Tendsto (fun k => (ν k a : ℝ)/(n k : ℝ)) atTop (𝓝 (γ*p a)))
    (hc : ∀ᶠ k in atTop, PartitionCompatible (μ k) (ν k)) (r : PositiveRoot d) :
    Tendsto (fun k => rootFraction (μ k) (fun a => ν k a-μ k a) r) atTop (𝓝 γ⁻¹) := by
  have hg : 0 < p r.val.1-p r.val.2 := sub_pos.mpr (hord r.property)
  have hq := ((hμ r.val.1).sub (hμ r.val.2)).div
    ((hν r.val.1).sub (hν r.val.2)) (by nlinarith : γ*p r.val.1-γ*p r.val.2 ≠ 0)
  have he : (p r.val.1-p r.val.2)/(γ*p r.val.1-γ*p r.val.2) = γ⁻¹ := by
    rw [← mul_sub]
    field_simp
  rw [he] at hq
  apply hq.congr'
  filter_upwards [hc, hn.eventually (eventually_gt_atTop 0)] with k hk hnk
  have hnreal : (n k : ℝ) ≠ 0 := by exact_mod_cast hnk.ne'
  have hgap : rootGap (μ k) r + rootGap (fun a => ν k a-μ k a) r = rootGap (ν k) r := by
    simp only [rootGap, Nat.cast_sub (hk.1 _)]
    ring
  rw [rootFraction, hgap]
  simp only [Pi.div_apply, ← sub_div, rootGap]
  field_simp

/-- All representation-theoretic hypotheses needed by the actual Cartan
state limit are derived from the two physical shrinking windows. -/
theorem typical_pair_cartan_parameters
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hm : Tendsto m atTop atTop)
    (μ ν : ℕ → Fin d → ℕ) (p : Fin d → ℝ) (hp : ∀ a, 0 < p a) (hord : StrictAnti p)
    (γ : ℝ) (hγ : 1 < γ)
    (hgain : Tendsto (fun k => (m k : ℝ)/(n k : ℝ)) atTop (𝓝 γ))
    (hμ : ∀ᶠ k in atTop, TypicalLabel (n k) p (μ k))
    (hν : ∀ᶠ k in atTop, TypicalLabel (m k) p (ν k)) :
    ∃ δμ δτ : ℕ → ℝ, Tendsto δμ atTop atTop ∧ Tendsto δτ atTop atTop ∧
      (∀ᶠ k in atTop, PartitionCompatible (μ k) (ν k)) ∧
      (∀ᶠ k in atTop, ∀ r : PositiveRoot d, δμ k ≤ rootGap (μ k) r) ∧
      (∀ᶠ k in atTop, ∀ r : PositiveRoot d, δτ k ≤ rootGap (fun a => ν k a-μ k a) r) ∧
      (∀ r : PositiveRoot d, Tendsto (fun k => rootFraction (μ k) (fun a => ν k a-μ k a) r)
        atTop (𝓝 γ⁻¹)) := by
  obtain ⟨hμlim,hνlim⟩ := typical_pair_scaled_limits n m hn hm μ ν p γ hgain hμ hν
  have hc := eventually_partitionCompatible_of_scaled_limits n hn μ ν p hp hord γ hγ hμlim hνlim
  have hτlim := difference_scaled_tendsto n μ ν p γ hμlim hνlim hc
  obtain ⟨δμ,hδμ,hgμ⟩ := exists_root_gap_of_scaled_limits n hn μ p hp hord hμlim
  obtain ⟨δτ,hδτ,hgτ⟩ := exists_root_gap_of_scaled_limits n hn (fun k a => ν k a-μ k a)
    (fun a => (γ-1)*p a) (fun a => mul_pos (sub_pos.mpr hγ) (hp a))
    (fun a b hab => mul_lt_mul_of_pos_left (hord hab) (sub_pos.mpr hγ)) hτlim
  exact ⟨δμ,δτ,hδμ,hδτ,hc,hgμ,hgτ,
    rootFraction_difference_tendsto n hn μ ν p hord γ (by linarith) hμlim hνlim hc⟩

end Cloning.TensorCloning
