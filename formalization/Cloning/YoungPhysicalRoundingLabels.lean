import Cloning.YoungPhysicalRoundingCoordinates
import Cloning.YoungPhysicalRoundingFallback

/-! Exact full-label PMF identities for the physical randomized Young kernel. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungHyperplane
open Cloning.TensorLie Cloning.YoungGeneral Cloning.YoungCompatibility
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem probability_map_injective {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (P : PMF A) (a : A) : probability (P.map f) (f a) = probability P a := by
  unfold probability
  congr 1
  rw [PMF.map_apply]
  simp only [hf.eq_iff]
  exact (tsum_eq_single a (fun b hb ↦ if_neg (Ne.symm hb))).trans (if_pos rfl)

theorem affinity_map_injective {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (P Q : PMF A) :
    CountableScheffe.affinity (probability (P.map f)) (probability (Q.map f)) =
      CountableScheffe.affinity (probability P) (probability Q) := by
  unfold CountableScheffe.affinity
  have hsupport : Function.support (fun b ↦ Real.sqrt (probability (P.map f) b)*
      Real.sqrt (probability (Q.map f) b)) ⊆ Set.range f := by
    intro b hb
    by_contra hn
    have hz : P.map f b = 0 := by
      rw [PMF.map_apply]
      have hzero (a : A) : (if b = f a then P a else 0) = 0 :=
        if_neg (fun h ↦ hn ⟨a, h.symm⟩)
      simp only [hzero, tsum_zero]
    change Real.sqrt (probability (P.map f) b)*Real.sqrt (probability (Q.map f) b) ≠ 0 at hb
    rw [probability, hz, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at hb
    exact hb rfl
  rw [← hf.tsum_eq hsupport]
  simp_rw [probability_map_injective f hf]

theorem complete_injective (d : ℕ) (m : ℤ) :
    Function.Injective (complete (d := d) m) := by
  intro x y h
  funext i
  simpa only [complete_head] using congrArg (fun z : Fin (d+1) → ℤ ↦ z i.castSucc) h

/-- The exact finite physical target law, retaining every row. -/
def tensorYoungIntegerPMF (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (Fin (d+1) → ℤ) :=
  (tensorYoungPMF N (d+1) p hp hs).map integerShape

theorem tensorYoungIntegerPMF_eq_complete_head (d N : ℕ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    tensorYoungIntegerPMF d N p hp hs = (tensorYoungHeadPMF d N p hp hs).map (complete N) := by
  rw [tensorYoungIntegerPMF, tensorYoungHeadPMF_eq_map, PMF.map_comp]
  apply PMF.ext
  intro z
  simp only [PMF.map_apply]
  apply tsum_congr
  intro μ
  by_cases hz : tensorYoungPMF N (d+1) p hp hs μ = 0
  · simp [hz]
  · have hmass : ∑ i, (μ i).val = N := by
      by_contra hh
      exact hz (physicalYoungPMF_eq_zero_of_not_partition _ _ _ _ _ _ μ (Or.inr hh))
    have he : complete N (fun i : Fin d ↦ ((μ i.castSucc).val : ℤ)) = integerShape μ := by
      funext i
      exact shapeLattice_apply d N μ hmass i
    simp only [Function.comp_apply, he]
    split_ifs <;> rfl

/-- Raw physical output on the full integer lattice. -/
def tensorYoungRawOutput (d n m : ℕ) (γ : ℝ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (Fin (d+1) → ℤ) :=
  (tensorYoungPMF n (d+1) p hp hs).bind (fun μ ↦ rawKernel γ m (integerShape μ))

def tensorYoungFallbackOutput (d n m : ℕ) (γ : ℝ) (p : Fin (d+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF (Fin (d+1) → ℤ) :=
  (tensorYoungPMF n (d+1) p hp hs).bind (fun μ ↦ fallbackKernel γ n m (integerShape μ))

theorem tensorYoungRawOutput_eq_complete_transport (d n m : ℕ) (γ : ℝ)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    tensorYoungRawOutput d n m γ p hp hs =
      (YoungRounding.transport γ (tensorYoungHeadPMF d n p hp hs)).map (complete m) := by
  rw [tensorYoungHeadPMF_eq_map, YoungRounding.transport, PMF.bind_map, PMF.map_bind]
  rfl

theorem tensorYoungRawOutput_affinity (d n m : ℕ) (γ : ℝ)
    (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    CountableScheffe.affinity (probability (tensorYoungRawOutput d n m γ p hp hs))
      (probability (tensorYoungIntegerPMF d m p hp hs)) =
    CountableScheffe.affinity
      (probability (YoungRounding.transport γ (tensorYoungHeadPMF d n p hp hs)))
      (probability (tensorYoungHeadPMF d m p hp hs)) := by
  rw [tensorYoungRawOutput_eq_complete_transport, tensorYoungIntegerPMF_eq_complete_head,
    affinity_map_injective _ (complete_injective d m)]

end Cloning.YoungHyperplane
