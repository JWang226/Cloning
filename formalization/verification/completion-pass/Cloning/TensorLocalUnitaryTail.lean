import Cloning.TensorLocalUnitaryGenerator
import Mathlib.Topology.Algebra.Order.Floor

/-! Uniform decay of the physical finite-cutoff Taylor remainder. -/
noncomputable section
open scoped BigOperators Topology
open Filter NormedSpace
open Cloning.TensorLie
namespace Cloning.TensorLocalUnitary
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

private theorem tendsto_succ_mul_pow_div_factorial (c : ℝ) :
    Tendsto (fun m : ℕ => ((m : ℝ)+1)*c^m/(m.factorial : ℝ)) atTop (𝓝 0) := by
  have h0 := FloorSemiring.tendsto_pow_div_factorial_atTop c
  have h1 := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (1 : ℝ) c 1
  have h := h0.add h1
  simp only [one_mul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have he : m = (m-1)+1 := by omega
  have hf : (m.factorial : ℝ) = (m : ℝ)*((m-1).factorial : ℝ) := by
    conv_lhs => rw [he, Nat.factorial_succ]
    push_cast
    rw [← Nat.cast_add_one, ← he]
  have hf0 : ((m-1).factorial : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [hf]
  field_simp
  <;> ring

/-- The square-root growth per generator step is dominated by the factorial
Taylor denominator. This is the analytic-vector estimate used uniformly in a
bounded displacement window. -/
theorem tendsto_sqrt_growth_div_factorial (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun m : ℕ => (B * Real.sqrt ((m : ℝ)+1))^(m+1) / (m.factorial : ℝ))
      atTop (𝓝 0) := by
  let q := B^2 * Real.exp 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hlim : Tendsto (fun m : ℕ => q * (((m : ℝ)+1)*q^m/(m.factorial : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_succ_mul_pow_div_factorial q).const_mul q
  have hsq (m : ℕ) :
      ((B * Real.sqrt ((m : ℝ)+1))^(m+1) / (m.factorial : ℝ))^2 ≤
        q * (((m : ℝ)+1)*q^m/(m.factorial : ℝ)) := by
    have hm : 0 ≤ (m : ℝ)+1 := by positivity
    have hf : (0 : ℝ) < m.factorial := by positivity
    have he := Real.pow_div_factorial_le_exp ((m : ℝ)+1) hm m
    have heq : Real.exp ((m : ℝ)+1) = (Real.exp 1)^(m+1) := by
      simpa using Real.exp_nat_mul 1 (m+1)
    rw [heq] at he
    calc
      _ = (B^2)^m * B^2 * ((m : ℝ)+1) /
          (m.factorial : ℝ) * (((m : ℝ)+1)^m/(m.factorial : ℝ)) := by
        rw [div_pow, ← pow_mul, mul_comm (m+1) 2, pow_mul, mul_pow,
          Real.sq_sqrt hm, mul_pow, pow_succ, pow_succ]
        ring
      _ ≤ (B^2)^m * B^2 * ((m : ℝ)+1) /
          (m.factorial : ℝ) * (Real.exp 1)^(m+1) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by dsimp [q]; rw [mul_pow, pow_succ]; ring
  have hs : Tendsto (fun m : ℕ =>
      ((B * Real.sqrt ((m : ℝ)+1))^(m+1) / (m.factorial : ℝ))^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hsq hlim
  have h := hs.sqrt
  have heq : (fun m : ℕ => Real.sqrt
      (((B * Real.sqrt ((m : ℝ)+1))^(m+1) / (m.factorial : ℝ))^2)) =
      (fun m : ℕ => (B * Real.sqrt ((m : ℝ)+1))^(m+1) / (m.factorial : ℝ)) := by
    funext m
    exact Real.sqrt_sq (by positivity)
  rw [heq, Real.sqrt_zero] at h
  exact h

/-- A single scalar envelope for every displacement in a fixed sum-norm ball. -/
def uniformTaylorBound (B : ℝ) (R d m : ℕ) : ℝ :=
  ((2*B) * Real.sqrt ((((R+(m+1)*d : ℕ) : ℝ)+1)*2))^(m+1) / (m.factorial : ℝ)

theorem uniformTaylorBound_nonneg (B : ℝ) (hB : 0 ≤ B) (R d m : ℕ) :
    0 ≤ uniformTaylorBound B R d m := by unfold uniformTaylorBound; positivity

theorem uniformTaylorBound_tendsto (B : ℝ) (hB : 0 ≤ B) (R d : ℕ) :
    Tendsto (uniformTaylorBound B R d) atTop (𝓝 0) := by
  let C := 2*B*Real.sqrt (2*((R : ℝ)+(d : ℝ)+1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply squeeze_zero (uniformTaylorBound_nonneg B hB R d)
    (fun m => ?_) (tendsto_sqrt_growth_div_factorial C hC)
  unfold uniformTaylorBound
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  calc
    _ ≤ (2*B) * Real.sqrt (2*((R : ℝ)+(d : ℝ)+1)*((m : ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by positivity)
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) R) (Nat.cast_nonneg (α := ℝ) m)]
    _ = C * Real.sqrt ((m : ℝ)+1) := by
      rw [Real.sqrt_mul (by positivity)]
      dsimp [C]
      ring

/-- Uniform approximation of the actual physical unitary on the complete unit
ball of a fixed cyclic cutoff, simultaneously over every bounded displacement.
The Taylor order is chosen before the partition size. -/
theorem exists_uniform_physical_taylor_order {d : ℕ}
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2)
    (B : ℝ) (hB : 0 ≤ B) (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ᶠ N in atTop, ∀ (z : PositiveRoot d → ℂ)
      (x : TensorRegister (∑ j, mu N j) (Fin d)),
      (∑ a, ‖z a‖) ≤ B →
      x ∈ cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (R : ℤ) →
      ‖x‖ ≤ 1 →
      ‖exp (rootGenerator (n := ∑ j, mu N j) (mu N) z) x -
        ∑ j ∈ Finset.range (m+1), ((j.factorial : ℝ)⁻¹) •
          ((rootGenerator (n := ∑ j, mu N j) (mu N) z ^ j) x)‖ < ε := by
  obtain ⟨m, hm⟩ := ((uniformTaylorBound_tendsto B hB R d).eventually_lt_const hε).exists
  refine ⟨m, ?_⟩
  have hlarge := hδ.eventually (eventually_ge_atTop
    (2 * (((R+(m+1)*d : ℕ) : ℝ)+1)))
  filter_upwards [hgap, hlarge] with N hg hL
  intro z x hz hx hn
  apply lt_of_le_of_lt _ hm
  have hg' (a : PositiveRoot d) := hL.trans (hg a)
  apply (exp_rootGenerator_taylor_remainder
    (partitionHighestTensor (mu N) (hmu N)) (mu N)
    (partitionHighestTensor_cartan (mu N) (hmu N))
    (partitionHighestTensor_raising_zero (mu N) (hmu N)) z R m hg' hx).trans
  unfold uniformTaylorBound
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (mul_le_mul_of_nonneg_left hn (by positivity)).trans
  rw [mul_one]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num))
    (Real.sqrt_nonneg _)

end Cloning.TensorLocalUnitary
