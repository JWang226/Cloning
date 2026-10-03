import Cloning.CountableScheffe
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Countable-PMF fallback bounds

Actual normalized PMFs are used throughout.  Replacing transition rows only off
a set of good inputs costs at most twice its probability mass in `ℓ¹`, even
when the input and output lattices are countably infinite.  The Hellinger
bound follows from the already proved countable affinity continuity theorem.
-/

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace Cloning.YoungCompatibility

variable {A B : Type*}

def probability (p : PMF A) (a : A) : ℝ := (p a).toReal

theorem probability_nonneg (p : PMF A) (a : A) : 0 ≤ probability p a :=
  ENNReal.toReal_nonneg

theorem hasSum_probability (p : PMF A) : HasSum (probability p) 1 := by
  have h := ENNReal.hasSum_toReal p.tsum_coe_ne_top
  have hsum : (∑' a, (p a).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe]
    simp
  simpa only [probability, hsum] using h

@[simp] theorem tsum_probability (p : PMF A) : ∑' a, probability p a = 1 :=
  (hasSum_probability p).tsum_eq

theorem probability_bind (p : PMF A) (K : A → PMF B) (b : B) :
    probability (p.bind K) b = ∑' a, probability p a * probability (K a) b := by
  unfold probability
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun a ↦ ENNReal.mul_ne_top
    (p.apply_ne_top a) ((K a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

theorem summable_kernel_joint (p : PMF A) (K : A → PMF B) :
    Summable (fun ab : A × B ↦ probability p ab.1 * probability (K ab.1) ab.2) := by
  rw [summable_prod_of_nonneg (fun ab ↦ mul_nonneg
    (probability_nonneg p ab.1) (probability_nonneg (K ab.1) ab.2))]
  constructor
  · intro a
    change Summable (fun b : B ↦ probability p a * probability (K a) b)
    exact (hasSum_probability (K a)).summable.mul_left (probability p a)
  change Summable (fun a : A ↦ ∑' b : B, probability p a * probability (K a) b)
  simpa only [tsum_mul_left, tsum_probability, mul_one] using (hasSum_probability p).summable

theorem summable_kernel_error (p : PMF A) (K L : A → PMF B) :
    Summable (fun ab : A × B ↦ probability p ab.1 *
      |probability (K ab.1) ab.2 - probability (L ab.1) ab.2|) := by
  apply ((summable_kernel_joint p K).add (summable_kernel_joint p L)).of_nonneg_of_le
  · intro ab
    exact mul_nonneg (probability_nonneg p ab.1) (abs_nonneg _)
  · intro ab
    have h := abs_sub (probability (K ab.1) ab.2) (probability (L ab.1) ab.2)
    rw [abs_of_nonneg (probability_nonneg _ _), abs_of_nonneg (probability_nonneg _ _)] at h
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h (probability_nonneg p ab.1)

theorem kernel_row_l1_le_two (K L : PMF B) :
    CountableScheffe.l1Distance (probability K) (probability L) ≤ 2 := by
  unfold CountableScheffe.l1Distance
  calc
    (∑' b, |probability K b - probability L b|) ≤
        ∑' b, (probability K b + probability L b) := by
      apply ((hasSum_probability K).summable.sub (hasSum_probability L).summable).abs.tsum_le_tsum
      · intro b
        simpa only [abs_of_nonneg (probability_nonneg K b),
          abs_of_nonneg (probability_nonneg L b)] using abs_sub (probability K b) (probability L b)
      · exact (hasSum_probability K).summable.add (hasSum_probability L).summable
    _ = 2 := by rw [(hasSum_probability K).summable.tsum_add (hasSum_probability L).summable]; norm_num [tsum_probability]

/-- Countable stochastic transport inequality, proved by absolutely summable
Fubini for the actual transition probabilities. -/
theorem bind_l1_kernel_bound (p : PMF A) (K L : A → PMF B) :
    CountableScheffe.l1Distance (probability (p.bind K)) (probability (p.bind L)) ≤
      ∑' a, probability p a * CountableScheffe.l1Distance (probability (K a)) (probability (L a)) := by
  have hK := summable_kernel_joint p K
  have hL := summable_kernel_joint p L
  have hE := summable_kernel_error p K L
  unfold CountableScheffe.l1Distance
  have hb (b : B) : |probability (p.bind K) b - probability (p.bind L) b| ≤
      ∑' a, probability p a * |probability (K a) b - probability (L a) b| := by
    have hKb : Summable (fun a : A ↦ probability p a * probability (K a) b) := hK.prod_symm.prod_factor b
    have hLb : Summable (fun a : A ↦ probability p a * probability (L a) b) := hL.prod_symm.prod_factor b
    rw [probability_bind, probability_bind, ← hKb.tsum_sub hLb]
    calc
      _ ≤ ∑' a, |probability p a * probability (K a) b - probability p a * probability (L a) b| := by
        have hnorm : Summable (fun a : A ↦ ‖probability p a * probability (K a) b -
            probability p a * probability (L a) b‖) := by
          simpa only [Real.norm_eq_abs] using (hKb.sub hLb).abs
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
      _ = _ := by
        apply tsum_congr
        intro a
        rw [← mul_sub, abs_mul, abs_of_nonneg (probability_nonneg p a)]
  calc
    _ ≤ ∑' b, ∑' a, probability p a * |probability (K a) b - probability (L a) b| := by
      exact ((hasSum_probability (p.bind K)).summable.sub
        (hasSum_probability (p.bind L)).summable).abs.tsum_le_tsum hb hE.prod_symm.prod
    _ = ∑' a, ∑' b, probability p a * |probability (K a) b - probability (L a) b| := hE.tsum_comm
    _ = _ := by simp only [tsum_mul_left]

/-- The bad-input probability, represented as an ordinary convergent real sum. -/
def badMass (p : PMF A) (good : A → Prop) : ℝ :=
  ∑' a, if good a then 0 else probability p a

theorem badMass_nonneg (p : PMF A) (good : A → Prop) : 0 ≤ badMass p good := by
  classical
  apply tsum_nonneg
  intro a
  split_ifs
  · exact le_rfl
  · exact probability_nonneg p a

theorem summable_badMass (p : PMF A) (good : A → Prop) :
    Summable (fun a ↦ if good a then 0 else probability p a) := by
  classical
  apply (hasSum_probability p).summable.of_nonneg_of_le
  · intro a
    split_ifs
    · exact le_rfl
    · exact probability_nonneg p a
  · intro a
    split_ifs <;> simp [probability_nonneg]

/-- Actual PMF fallback has dimension-independent cost.  The equality hypothesis
is a row identity on the good inputs; the concrete Young-label file derives it
from strict spectral gaps and the actual rounding support. -/
theorem bind_fallback_l1_bound (p : PMF A) (K L : A → PMF B)
    (good : A → Prop) (hsame : ∀ a, good a → K a = L a) :
    CountableScheffe.l1Distance (probability (p.bind K)) (probability (p.bind L)) ≤
      2 * badMass p good := by
  classical
  apply (bind_l1_kernel_bound p K L).trans
  have hs : Summable (fun a ↦ probability p a *
      CountableScheffe.l1Distance (probability (K a)) (probability (L a))) := by
    simpa only [CountableScheffe.l1Distance, tsum_mul_left] using (summable_kernel_error p K L).prod
  calc
    _ ≤ ∑' a, 2 * (if good a then 0 else probability p a) := by
      apply hs.tsum_le_tsum _ ((summable_badMass p good).mul_left 2)
      intro a
      by_cases ha : good a
      · simp [ha, hsame a ha, CountableScheffe.l1Distance]
      · simp only [ha, ↓reduceIte]
        calc
          _ ≤ probability p a * 2 := mul_le_mul_of_nonneg_left
            (kernel_row_l1_le_two (K a) (L a)) (probability_nonneg p a)
          _ = _ := mul_comm _ _
    _ = _ := by rw [tsum_mul_left]; rfl

theorem bind_fallback_affinity_bound (p : PMF A) (K L : A → PMF B)
    (good : A → Prop) (hsame : ∀ a, good a → K a = L a) (q : PMF B) :
    |CountableScheffe.affinity (probability (p.bind K)) (probability q) -
      CountableScheffe.affinity (probability (p.bind L)) (probability q)| ≤
      Real.sqrt (2 * badMass p good) :=
  (CountableScheffe.affinity_l1_continuity _ _ _
    (probability_nonneg _) (probability_nonneg _) (probability_nonneg _)
    (hasSum_probability _).summable (hasSum_probability _).summable
    (hasSum_probability _)).trans
    (Real.sqrt_le_sqrt (bind_fallback_l1_bound p K L good hsame))

end Cloning.YoungCompatibility
