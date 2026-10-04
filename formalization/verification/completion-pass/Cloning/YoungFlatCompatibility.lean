import Cloning.YoungFlatCells
import Cloning.TensorCloningChannel

/-! Common-point quantization of the flat limit gives actual compatible partitions. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungFlat
open Cloning.YoungHyperplane Cloning.YoungGeneral Cloning.TensorCloning Cloning.TensorLie
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem sampleShape_flat_ratio_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (x : rootSpace d) (i : Fin (d+1)) :
    Tendsto (fun k ↦ ((sampleShape d (n k) (flatSpectrum (d+1)) x i).val : ℝ)/(n k : ℝ))
      atTop (𝓝 (1/((d+1 : ℕ) : ℝ))) := by
  apply (sampleLabel_flat_moving_ratio d n hn (fun _ ↦ x) x (fun _ ↦ tendsto_const_nhds) i).congr'
  filter_upwards [eventually_flat_sampleShape_valid d n hn (fun _ ↦ x) x
    (fun _ ↦ tendsto_const_nhds)] with k hk
  have he := shapeLattice_apply d (n k) (sampleShape d (n k) (flatSpectrum (d+1)) x) hk.1 i
  rw [hk.2] at he
  have hr : ((sampleLabel d (n k) (flatSpectrum (d+1)) x).1 i : ℝ) =
      ((sampleShape d (n k) (flatSpectrum (d+1)) x i).val : ℝ) := by exact_mod_cast he
  rw [hr]

theorem sampleShape_flat_gap_tendsto (d : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (x : rootSpace d) (i j : Fin (d+1)) :
    Tendsto (fun k ↦ (((sampleShape d (n k) (flatSpectrum (d+1)) x i).val : ℝ)-
      ((sampleShape d (n k) (flatSpectrum (d+1)) x j).val : ℝ))/Real.sqrt (n k : ℝ))
      atTop (𝓝 (x.1 i-x.1 j)) := by
  have hc a := sampleLabel_center_tendsto d n hn (fun _ ↦ flatSpectrum (d+1))
    (fun _ ↦ flatSpectrum_sum _ (by omega)) x a
  apply ((hc i).sub (hc j)).congr'
  filter_upwards [eventually_flat_sampleShape_valid d n hn (fun _ ↦ x) x
    (fun _ ↦ tendsto_const_nhds)] with k hk
  rw [← hk.2]
  simp only [sampleCenter_apply d (n k) _ (flatSpectrum_sum _ (by omega)),
    shapeLattice_apply d (n k) _ hk.1, Int.cast_natCast, flatSpectrum]
  ring

theorem eventually_flat_sampleShape_antitone (d : ℕ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (x : rootSpace d) (hx : StrictAnti (fun i ↦ x.1 i)) :
    ∀ᶠ k in atTop, Antitone (fun i ↦ (sampleShape d (n k) (flatSpectrum (d+1)) x i).val) := by
  have he : ∀ᶠ k in atTop, ∀ r : PositiveRoot (d+1),
      0 < (((sampleShape d (n k) (flatSpectrum (d+1)) x r.val.1).val : ℝ)-
        ((sampleShape d (n k) (flatSpectrum (d+1)) x r.val.2).val : ℝ))/Real.sqrt (n k : ℝ) :=
    eventually_all.mpr fun r ↦ (sampleShape_flat_gap_tendsto d n hn x r.val.1 r.val.2).eventually
      (eventually_gt_nhds (sub_pos.mpr (hx r.property)))
  filter_upwards [he, hn.eventually (eventually_gt_atTop 0)] with k hk hn0
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  have hh := hk ⟨(i,j),hij⟩
  have hs : 0 < Real.sqrt (n k : ℝ) := by positivity
  have hreal := (div_pos_iff_of_pos_right hs).mp hh
  exact_mod_cast (sub_pos.mp hreal).le

theorem sampleShape_flat_cross_gap_tendsto (d : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ)
    (hratio : Tendsto (fun N : ℕ ↦ (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (x : rootSpace d) (i j : Fin (d+1)) :
    Tendsto (fun N : ℕ ↦
      ((((sampleShape d (m N) (flatSpectrum (d+1)) x i).val : ℝ)-
          ((sampleShape d (m N) (flatSpectrum (d+1)) x j).val : ℝ))-
        (((sampleShape d N (flatSpectrum (d+1)) x i).val : ℝ)-
          ((sampleShape d N (flatSpectrum (d+1)) x j).val : ℝ)))/Real.sqrt (N : ℝ))
      atTop (𝓝 ((Real.sqrt γ-1)*(x.1 i-x.1 j))) := by
  have hs : Tendsto (fun N : ℕ ↦ Real.sqrt (m N : ℝ)/Real.sqrt (N : ℝ)) atTop
      (𝓝 (Real.sqrt γ)) := by
    simpa only [Real.sqrt_div (Nat.cast_nonneg _)] using hratio.sqrt
  have hh := (hs.mul (sampleShape_flat_gap_tendsto d m hm x i j)).sub
    (sampleShape_flat_gap_tendsto d id tendsto_id x i j)
  have he : Real.sqrt γ*(x.1 i-x.1 j)-(x.1 i-x.1 j) =
      (Real.sqrt γ-1)*(x.1 i-x.1 j) := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0, hm.eventually (eventually_gt_atTop 0)] with N hN hmN
  have hmn : Real.sqrt (m N : ℝ) ≠ 0 := by positivity
  have hn : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  dsimp only [id]
  field_simp
  <;> ring

theorem eventually_flat_sampleShape_dominates (d : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ ↦ (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (x : rootSpace d) :
    ∀ᶠ N in atTop, ∀ i, (sampleShape d N (flatSpectrum (d+1)) x i).val ≤
      (sampleShape d (m N) (flatSpectrum (d+1)) x i).val := by
  have hi i : Tendsto (fun N : ℕ ↦
      (((sampleShape d (m N) (flatSpectrum (d+1)) x i).val : ℝ)-
        ((sampleShape d N (flatSpectrum (d+1)) x i).val : ℝ))/(N : ℝ))
      atTop (𝓝 ((γ-1)/((d+1 : ℕ) : ℝ))) := by
    have hh := ((sampleShape_flat_ratio_tendsto d m hm x i).mul hratio).sub
      (sampleShape_flat_ratio_tendsto d id tendsto_id x i)
    have he : 1/((d+1 : ℕ) : ℝ)*γ-1/((d+1 : ℕ) : ℝ) = (γ-1)/((d+1 : ℕ) : ℝ) := by ring
    rw [he] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0, hm.eventually (eventually_gt_atTop 0)] with N hN hmN
    have hm0 : (m N : ℝ) ≠ 0 := by positivity
    have hn0 : (N : ℝ) ≠ 0 := by positivity
    dsimp only [id]
    field_simp
    <;> ring
  have he : ∀ᶠ N in atTop, ∀ i,
      0 < (((sampleShape d (m N) (flatSpectrum (d+1)) x i).val : ℝ)-
        ((sampleShape d N (flatSpectrum (d+1)) x i).val : ℝ))/(N : ℝ) :=
    eventually_all.mpr fun i ↦ (hi i).eventually
      (eventually_gt_nhds (div_pos (sub_pos.mpr hγ) (by positivity)))
  filter_upwards [he, eventually_gt_atTop 0] with N hN hN0
  intro i
  have hn : (0 : ℝ)<N := by exact_mod_cast hN0
  exact_mod_cast (sub_pos.mp ((div_pos_iff_of_pos_right hn).mp (hN i))).le

/-- At each strictly ordered limiting point, the literal rounded finite labels
are eventually compatible for the actual Cartan channel. -/
theorem eventually_flat_sampleShape_compatible (d : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ ↦ (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ))
    (x : rootSpace d) (hx : StrictAnti (fun i ↦ x.1 i)) :
    ∀ᶠ N in atTop, PartitionCompatible
      (fun i ↦ (sampleShape d N (flatSpectrum (d+1)) x i).val)
      (fun i ↦ (sampleShape d (m N) (flatSpectrum (d+1)) x i).val) := by
  have hsqrt : 1<Real.sqrt γ := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ)≤1) hγ
  have he : ∀ᶠ N in atTop, ∀ r : PositiveRoot (d+1),
      0 < ((((sampleShape d (m N) (flatSpectrum (d+1)) x r.val.1).val : ℝ)-
          ((sampleShape d (m N) (flatSpectrum (d+1)) x r.val.2).val : ℝ))-
        (((sampleShape d N (flatSpectrum (d+1)) x r.val.1).val : ℝ)-
          ((sampleShape d N (flatSpectrum (d+1)) x r.val.2).val : ℝ)))/Real.sqrt (N : ℝ) :=
    eventually_all.mpr fun r ↦ (sampleShape_flat_cross_gap_tendsto d m hm γ hratio x r.val.1 r.val.2).eventually
      (eventually_gt_nhds (mul_pos (sub_pos.mpr hsqrt) (sub_pos.mpr (hx r.property))))
  filter_upwards [he, eventually_flat_sampleShape_dominates d m hm γ hγ hratio x,
    eventually_gt_atTop 0] with N hgap hdom hN
  refine ⟨hdom, ?_⟩
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  have hh := hgap ⟨(i,j),hij⟩
  have hn : 0<Real.sqrt (N : ℝ) := by positivity
  have hreal := (div_pos_iff_of_pos_right hn).mp hh
  have ht :
      (((sampleShape d (m N) (flatSpectrum (d+1)) x j).val-
        (sampleShape d N (flatSpectrum (d+1)) x j).val : ℕ) : ℝ) ≤
      (((sampleShape d (m N) (flatSpectrum (d+1)) x i).val-
        (sampleShape d N (flatSpectrum (d+1)) x i).val : ℕ) : ℝ) := by
    rw [Nat.cast_sub (hdom i), Nat.cast_sub (hdom j)]
    linarith
  exact_mod_cast ht

end Cloning.YoungFlat
