import Cloning.TensorCloningChannel
import Cloning.TensorSchurDecompositionMultiplicity
import Cloning.YoungHookVandermonde
import Cloning.YoungCompatibilityFallback
import Mathlib.Probability.Distributions.Uniform

/-! The actual normalized randomized Young-label cloning kernel, distributed
uniformly across physical multiplicity copies. -/
noncomputable section
open scoped BigOperators Classical ENNReal
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral Cloning.YoungCompatibility
open Cloning.PCT Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem standardCount_pos {d n : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ) (hn : ∑ i, μ i = n) :
    0 < standardCount n μ := by
  have h : (0 : ℝ) < (standardCount n μ : ℝ) := by
    rw [standardCount_eq_vandermonde μ hμ hn]
    apply mul_pos
    · apply mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
      apply Finset.prod_pos
      intro i hi
      apply Finset.prod_pos
      intro j hj
      apply sub_pos.mpr
      exact_mod_cast shiftedRow_strictAnti μ hμ (Finset.mem_Ioi.mp hj)
    · apply Finset.prod_pos
      intro i hi
      exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))
  exact_mod_cast h

/-- Every actual partition occurs among the physical Schur copies. -/
theorem exists_copy_weight {n d : ℕ} (μ : Fin d → ℕ) (hμ : Antitone μ)
    (hn : ∑ i, μ i = n) :
    ∃ j : SchurCopy n d, ((recursivePhysicalDecomposition n d).get j).weight = μ := by
  have hc := recursivePhysicalDecomposition_copyCount n d μ
  have hp : 0 < physicalCopyCount (recursivePhysicalDecomposition n d) μ := by
    rw [hc]
    exact standardCount_pos μ hμ hn
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

def oneRowPartition (n d : ℕ) : Fin (d+1) → ℕ := fun i ↦ if i = 0 then n else 0

theorem oneRowPartition_antitone (n d : ℕ) : Antitone (oneRowPartition n d) := by
  intro i j hij
  by_cases hi : i = 0
  · simp only [oneRowPartition, hi, if_true]
    split_ifs <;> omega
  · have hj : j ≠ 0 := by intro hj; exact hi (le_antisymm (hj ▸ hij) (Fin.zero_le _))
    simp [oneRowPartition, hi, hj]

@[simp] theorem oneRowPartition_sum (n d : ℕ) : ∑ i, oneRowPartition n d i = n := by
  simp [oneRowPartition]

def fallbackCopy (n d : ℕ) : SchurCopy n (d+1) :=
  Classical.choose (exists_copy_weight (oneRowPartition n d) (oneRowPartition_antitone n d)
    (oneRowPartition_sum n d))

theorem fallbackCopy_weight (n d : ℕ) :
    ((recursivePhysicalDecomposition n (d+1)).get (fallbackCopy n d)).weight = oneRowPartition n d :=
  Classical.choose_spec (exists_copy_weight (oneRowPartition n d) (oneRowPartition_antitone n d)
    (oneRowPartition_sum n d))

section Fiber
variable {ι Λ : Type*} [Fintype ι] [DecidableEq Λ]

def uniformFiberPMF (label : ι → Λ) (i₀ : ι) (a : Λ) : PMF ι :=
  if h : (Finset.univ.filter (fun i ↦ label i = a)).Nonempty then
    PMF.uniformOfFinset (Finset.univ.filter (fun i ↦ label i = a)) h
  else PMF.pure i₀

theorem uniformFiberPMF_apply (label : ι → Λ) (i₀ : ι) (a : Λ)
    (h : ∃ i, label i = a) (j : ι) :
    uniformFiberPMF label i₀ a j =
      if label j = a then ((Finset.univ.filter (fun i ↦ label i = a)).card : ℝ≥0∞)⁻¹ else 0 := by
  have hn : (Finset.univ.filter (fun i ↦ label i = a)).Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  simp [uniformFiberPMF, hn]

theorem uniformFiberPMF_label (label : ι → Λ) (i₀ : ι) (a : Λ)
    (h : ∃ i, label i = a) : (uniformFiberPMF label i₀ a).map label = PMF.pure a := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  simp_rw [uniformFiberPMF_apply label i₀ a h]
  by_cases hb : b = a
  · subst b
    have he : (∑' i, if a = label i then uniformFiberPMF label i₀ a i else 0) = 1 := by
      rw [show (fun i ↦ if a = label i then uniformFiberPMF label i₀ a i else 0) =
          uniformFiberPMF label i₀ a by
        funext i
        rw [uniformFiberPMF_apply label i₀ a h]
        by_cases hi : label i = a <;> simp [hi, eq_comm]]
      exact (uniformFiberPMF label i₀ a).tsum_coe
    simpa only [uniformFiberPMF_apply label i₀ a h, PMF.pure_apply, if_true] using he
  · rw [PMF.pure_apply, if_neg hb]
    simp only [tsum_fintype]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hj : label i = a <;> simp [hj, hb, eq_comm]

end Fiber

def integerCopyLabel (n d : ℕ) (i : SchurCopy n (d+1)) : Fin (d+1) → ℤ :=
  fun a ↦ (((recursivePhysicalDecomposition n (d+1)).get i).weight a : ℤ)

/-- The spectrum-independent randomized output-copy law is constructed by
composing the normalized manuscript fallback kernel with uniform multiplicity
sampling. It is a genuine PMF for every finite sample size. -/
def universalCopyPMF (n m d : ℕ) (i : SchurCopy n (d+1)) : PMF (SchurCopy m (d+1)) :=
  (fallbackKernel ((m : ℝ) / (n : ℝ)) (n : ℤ) (m : ℤ) (integerCopyLabel n d i)).bind
    (uniformFiberPMF (integerCopyLabel m d) (fallbackCopy m d))

/-- Actual global cloning channel with no spectral parameter in its
construction, defined at all sample sizes (including n=0). -/
def universalChannel (n m d : ℕ) :
    QuantumChannel (TensorRegister n (Fin (d+1))) (TensorRegister m (Fin (d+1))) :=
  channel n m (d+1) (fun i j ↦ (universalCopyPMF n m d i j).toReal)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (fun i ↦ by
      simpa only [probability, tsum_fintype] using (hasSum_probability (universalCopyPMF n m d i)).tsum_eq)

end Cloning.TensorCloning
