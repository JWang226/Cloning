import Cloning.TensorPBWWeight
import Cloning.TensorCyclicSector

/-! The top Cartan weight of an actual cyclic highest sector is a line. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem loweringWeight_ne_zero_of_ne_nil (w : List (PositiveRoot d)) (hw : w ≠ []) :
    loweringWeight w ≠ 0 := by
  intro hz
  have hh := loweringWeight_index_sum w
  rw [hz] at hh
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hh
  cases w with
  | nil => exact hw rfl
  | cons a w =>
      have ha := a.height_pos
      simp only [loweringHeight] at hh
      omega

theorem inner_loweringWord_topWeight_eq_zero
    (Ω x : TensorRegister n (Fin d)) (mu : Fin d → ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hxweight : ∀ a, collectiveGenerator n a a x = (mu a : ℂ) • x)
    (w : List (PositiveRoot d)) (hw : w ≠ []) :
    ⟪loweringWord Ω w, x⟫_ℂ = 0 := by
  have hn := loweringWeight_ne_zero_of_ne_nil w hw
  obtain ⟨a, ha⟩ : ∃ a, loweringWeight w a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  have he : ((mu a : ℂ) + (loweringWeight w a : ℂ)) * ⟪loweringWord Ω w, x⟫_ℂ =
      (mu a : ℂ) * ⟪loweringWord Ω w, x⟫_ℂ := by
    calc
      _ = ⟪collectiveGenerator n a a (loweringWord Ω w), x⟫_ℂ := by
        rw [cartan_loweringWord Ω (fun a => (mu a : ℂ)) hweight]
        simp [inner_smul_left]
      _ = ⟪loweringWord Ω w, collectiveGenerator n a a x⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right, collectiveGenerator_adjoint]
      _ = _ := by rw [hxweight, inner_smul_right]
  have hz : (loweringWeight w a : ℂ) * ⟪loweringWord Ω w, x⟫_ℂ = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast ha)

/-- No raising or irreducibility premise is needed: the exact lowering weights
already force the full top-weight slice to be the original highest line. -/
theorem cyclicSector_cartanWeight_eq_highest_line
    (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (hΩ : ‖Ω‖ = 1)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω)
    (hxweight : ∀ a, collectiveGenerator n a a x = (mu a : ℂ) • x) :
    x = ⟪Ω, x⟫_ℂ • Ω := by
  let y := x - ⟪Ω, x⟫_ℂ • Ω
  have hy : y ∈ cyclicSector Ω := (cyclicSector Ω).sub_mem hx
    ((cyclicSector Ω).smul_mem _ (highest_mem_cyclicSector Ω))
  have hyweight : ∀ a, collectiveGenerator n a a y = (mu a : ℂ) • y := by
    intro a
    simp only [y, map_sub, map_smul, hxweight, hweight, smul_sub, smul_smul]
    rw [mul_comm (⟪Ω, x⟫_ℂ)]
  have hΩinner : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  have hΩy : ⟪Ω, y⟫_ℂ = 0 := by
    simp only [y, inner_sub_right, inner_smul_right, hΩinner, mul_one, sub_self]
  have horth : ∀ z ∈ cyclicSector Ω, ⟪z, y⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      cases w with
      | nil => exact hΩy
      | cons a w =>
        exact inner_loweringWord_topWeight_eq_zero Ω y mu hweight hyweight (a :: w) (by simp)
    | zero => simp
    | add u v hu hv ihu ihv => simp [inner_add_left, ihu, ihv]
    | smul c z hz ih => simp [inner_smul_left, ih]
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp (horth y hy))

end Cloning.TensorLie
