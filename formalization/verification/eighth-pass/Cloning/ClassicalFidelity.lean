import Cloning.Rounding
import Cloning.BlockFidelity

/-!
# Classical Hellinger affinity under perturbation and stochastic kernels

These proofs establish the finite classical instances of the continuity and
data-processing arguments used for Young-label laws. The limit theorems allow
the input and output label types to change with the sample size. They do not
formalize the continuous Gaussian density calculations.
-/

noncomputable section
open scoped BigOperators
open Filter Cloning.Rounding Cloning.BlockFidelity

namespace Cloning.ClassicalFidelity

theorem sqrt_difference_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact sqrt_sub_sqrt_le_sqrt_sub hy h
  · rw [abs_sub_comm, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact sqrt_sub_sqrt_le_sqrt_sub hx h

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Dimension-independent one-sided Hellinger continuity. Only the target
distribution needs normalization; the perturbed measures may have any mass. -/
theorem affinity_l1_continuity (p q r : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hrsum : ∑ i, r i = 1) :
    |classicalAffinity p r - classicalAffinity q r| ≤ Real.sqrt (l1Distance p q) := by
  calc
    |classicalAffinity p r - classicalAffinity q r| =
        |∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) * Real.sqrt (r i)| := by
      simp [classicalAffinity, Finset.sum_sub_distrib, sub_mul]
    _ ≤ ∑ i, |(Real.sqrt (p i) - Real.sqrt (q i)) * Real.sqrt (r i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, Real.sqrt |p i - q i| * Real.sqrt (r i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (sqrt_difference_bound _ _ (hp i) (hq i)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (∑ i, |p i - q i|) * Real.sqrt (∑ i, r i) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i ↦ abs_nonneg _) hr
    _ = Real.sqrt (l1Distance p q) := by rw [hrsum, Real.sqrt_one, mul_one]; rfl

/-- Varying both distributions costs the sum of the two square-root errors. -/
theorem affinity_l1_continuity_two_sided (p q p' q' : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp' : ∀ i, 0 ≤ p' i) (hq' : ∀ i, 0 ≤ q' i)
    (hp'sum : ∑ i, p' i = 1) (hqsum : ∑ i, q i = 1) :
    |classicalAffinity p q - classicalAffinity p' q'| ≤
      Real.sqrt (l1Distance p p') + Real.sqrt (l1Distance q q') := by
  calc
    |classicalAffinity p q - classicalAffinity p' q'| ≤
        |classicalAffinity p q - classicalAffinity p' q| +
          |classicalAffinity p' q - classicalAffinity p' q'| := abs_sub_le _ _ _
    _ ≤ Real.sqrt (l1Distance p p') + Real.sqrt (l1Distance q q') := by
      apply add_le_add (affinity_l1_continuity _ _ _ hp hp' hq hqsum)
      rw [classicalAffinity_comm p' q, classicalAffinity_comm p' q']
      exact affinity_l1_continuity _ _ _ hq hq' hp' hp'sum

theorem sqrt_kernel_identity (p q k : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hk : 0 ≤ k) :
    Real.sqrt (p * k) * Real.sqrt (q * k) = Real.sqrt p * Real.sqrt q * k := by
  rw [Real.sqrt_mul hp, Real.sqrt_mul hq]
  calc
    (Real.sqrt p * Real.sqrt k) * (Real.sqrt q * Real.sqrt k) =
        Real.sqrt p * Real.sqrt q * (Real.sqrt k * Real.sqrt k) := by ring
    _ = Real.sqrt p * Real.sqrt q * k := by rw [Real.mul_self_sqrt hk]

/-- Classical fidelity cannot decrease under a stochastic kernel. -/
theorem affinity_data_processing (K : StochasticKernel ι κ) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    classicalAffinity p q ≤ classicalAffinity (transport K p) (transport K q) := by
  have hcolumn (j : κ) :
      (∑ i, Real.sqrt (p i) * Real.sqrt (q i) * K.value i j) ≤
        Real.sqrt (transport K p j) * Real.sqrt (transport K q j) := by
    calc
      (∑ i, Real.sqrt (p i) * Real.sqrt (q i) * K.value i j) =
          ∑ i, Real.sqrt (p i * K.value i j) * Real.sqrt (q i * K.value i j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (sqrt_kernel_identity _ _ _ (hp i) (hq i) (K.nonneg i j)).symm
      _ ≤ Real.sqrt (transport K p j) * Real.sqrt (transport K q j) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun i ↦ mul_nonneg (hp i) (K.nonneg i j))
          (fun i ↦ mul_nonneg (hq i) (K.nonneg i j))
  calc
    classicalAffinity p q = ∑ j, ∑ i, Real.sqrt (p i) * Real.sqrt (q i) * K.value i j := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, K.row_sum, mul_one, classicalAffinity]
    _ ≤ classicalAffinity (transport K p) (transport K q) :=
      Finset.sum_le_sum fun j _ ↦ hcolumn j

/-- Continuity remains valid when the finite label alphabet grows with `n`. -/
theorem affinity_perturbation_tendsto {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (p q r : (n : ℕ) → I n → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ n i, 0 ≤ q n i) (hr : ∀ n i, 0 ≤ r n i)
    (hrsum : ∀ n, ∑ i, r n i = 1)
    (hl1 : Tendsto (fun n ↦ l1Distance (p n) (q n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ |classicalAffinity (p n) (r n) - classicalAffinity (q n) (r n)|)
      atTop (nhds 0) := by
  apply squeeze_zero (fun n ↦ abs_nonneg _)
    (fun n ↦ affinity_l1_continuity _ _ _ (hp n) (hq n) (hr n) (hrsum n))
  simpa using (Real.continuous_sqrt.tendsto 0).comp hl1

/-- An `L¹`-small change of labels preserves an already established affinity limit. -/
theorem affinity_limit_transfer {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (p q r : (n : ℕ) → I n → ℝ) (c : ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hq : ∀ n i, 0 ≤ q n i) (hr : ∀ n i, 0 ≤ r n i)
    (hrsum : ∀ n, ∑ i, r n i = 1)
    (hl1 : Tendsto (fun n ↦ l1Distance (p n) (q n)) atTop (nhds 0))
    (hlimit : Tendsto (fun n ↦ classicalAffinity (q n) (r n)) atTop (nhds c)) :
    Tendsto (fun n ↦ classicalAffinity (p n) (r n)) atTop (nhds c) := by
  have herr := affinity_perturbation_tendsto p q r hp hq hr hrsum hl1
  rw [tendsto_iff_dist_tendsto_zero] at hlimit ⊢
  simp only [Real.dist_eq] at hlimit ⊢
  apply squeeze_zero (fun n ↦ abs_nonneg _)
    (fun n ↦ abs_sub_le (classicalAffinity (p n) (r n))
      (classicalAffinity (q n) (r n)) c)
  simpa using herr.add hlimit

/-- Uniform continuity for families of distributions on growing alphabets. -/
theorem affinity_uniform_perturbation {I : ℕ → Type*} [∀ n, Fintype (I n)]
    {P : Type*} (S : Set P) (p q r : (n : ℕ) → P → I n → ℝ) (e : ℕ → ℝ)
    (hp : ∀ n s i, 0 ≤ p n s i) (hq : ∀ n s i, 0 ≤ q n s i)
    (hr : ∀ n s i, 0 ≤ r n s i) (hrsum : ∀ n s, ∑ i, r n s i = 1)
    (hl1 : ∀ n s, s ∈ S → l1Distance (p n s) (q n s) ≤ e n)
    (he : Tendsto e atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ S,
      |classicalAffinity (p n s) (r n s) - classicalAffinity (q n s) (r n s)| < ε := by
  have hroot : Tendsto (fun n ↦ Real.sqrt (e n)) atTop (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp he
  intro ε hε
  refine (hroot.eventually (gt_mem_nhds hε)).mono ?_
  intro n hn s hs
  calc
    |classicalAffinity (p n s) (r n s) - classicalAffinity (q n s) (r n s)| ≤
        Real.sqrt (l1Distance (p n s) (q n s)) :=
      affinity_l1_continuity _ _ _ (hp n s) (hq n s) (hr n s) (hrsum n s)
    _ ≤ Real.sqrt (e n) := Real.sqrt_le_sqrt (hl1 n s hs)
    _ < ε := hn

/-- The fallback `L¹` limit with sample-size-dependent input and output alphabets. -/
theorem fallback_l1_tendsto_dependent
    {I J : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Fintype (J n)]
    (K L : (n : ℕ) → StochasticKernel (I n) (J n))
    (p : (n : ℕ) → I n → ℝ) (hp : ∀ n i, 0 ≤ p n i)
    (good : (n : ℕ) → I n → Prop) [∀ n, DecidablePred (good n)]
    (hsame : ∀ n i, good n i → ∀ j, (K n).value i j = (L n).value i j)
    (hbad : Tendsto (fun n ↦ ∑ i, if good n i then 0 else p n i) atTop (nhds 0)) :
    Tendsto (fun n ↦ l1Distance (transport (K n) (p n)) (transport (L n) (p n)))
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun n ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg _)
    (fun n ↦ fallback_l1_bound (K n) (L n) (p n) (hp n) (good n) (hsame n))
  simpa [two_mul] using hbad.add hbad

/-- A fallback confined to asymptotically negligible inputs leaves the
label affinity unchanged, even for growing label alphabets. -/
theorem fallback_affinity_tendsto
    {I J : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Fintype (J n)]
    (K L : (n : ℕ) → StochasticKernel (I n) (J n))
    (p : (n : ℕ) → I n → ℝ) (r : (n : ℕ) → J n → ℝ)
    (hp : ∀ n i, 0 ≤ p n i) (hr : ∀ n j, 0 ≤ r n j)
    (hrsum : ∀ n, ∑ j, r n j = 1)
    (good : (n : ℕ) → I n → Prop) [∀ n, DecidablePred (good n)]
    (hsame : ∀ n i, good n i → ∀ j, (K n).value i j = (L n).value i j)
    (hbad : Tendsto (fun n ↦ ∑ i, if good n i then 0 else p n i) atTop (nhds 0)) :
    Tendsto (fun n ↦
      |classicalAffinity (transport (K n) (p n)) (r n) -
        classicalAffinity (transport (L n) (p n)) (r n)|) atTop (nhds 0) := by
  apply affinity_perturbation_tendsto
    (fun n ↦ transport (K n) (p n)) (fun n ↦ transport (L n) (p n)) r
    (fun n ↦ transport_nonneg (K n) (p n) (hp n))
    (fun n ↦ transport_nonneg (L n) (p n) (hp n)) hr hrsum
  exact fallback_l1_tendsto_dependent K L p hp good hsame hbad

end Cloning.ClassicalFidelity
