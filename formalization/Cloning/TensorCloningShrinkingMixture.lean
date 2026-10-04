import Cloning.TensorCloningShrinkingWindows

/-! Reindexing the uniform shrinking-window estimate onto any finite source
family, retaining uniformity in its cardinality and probability law. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical Topology
open Filter
namespace Cloning.TensorCloning
open Cloning.PCT Cloning.TensorLie Cloning.TensorLAN Cloning.InfiniteTraceClass Cloning.Hybrid
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local instance (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem eventually_uniform_shrinkingWindow_mixture_fidelity_fintype
    (K : Set (SimpleSpectrum d)) (hK : IsCompact K)
    (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ (n : ℕ) in atTop,∀ p∈K,∀ (J : Type*) [Fintype J],
      ∀ (μ : J → Fin d → ℕ) (ν : Fin d → ℕ)
        (hμ : ∀ j,Antitone (μ j)) (hν : Antitone ν),
      (∀ j a,|(μ j a : ℝ)/n-p.eigenvalue a|≤δ n) →
      (∀ a,|(ν a : ℝ)/(m n : ℝ)-p.eigenvalue a|≤δ n) →
      ∀ (q : J → ℝ) (hq : ∀ j,0≤q j),(∑ j,q j)=1 →
      |(partitionTransitionMixture μ ν hμ hν p.eigenvalue p.positive q hq).rootFidelity
        (partitionGibbsPositive ν hν p.eigenvalue p.positive)-orbitalValue γ p|<ε := by
  filter_upwards [eventually_uniform_shrinkingWindow_mixture_fidelity K hK m γ hγ hgain δ hδ ε hε]
    with n hn p hp J inst μ ν hμ hν hmc hnc q hq hs
  let e := (Fintype.equivFin J).symm
  have hqs : (∑ j : Fin (Fintype.card J),q (e j))=1 := (e.sum_comp q).trans hs
  have hh := hn p hp (Fintype.card J) (fun j => μ (e j)) ν (fun j => hμ (e j)) hν
    (fun j => hmc (e j)) hnc (fun j => q (e j)) (fun j => hq (e j)) hqs
  have he : partitionTransitionMixture (fun j => μ (e j)) ν (fun j => hμ (e j)) hν
      p.eigenvalue p.positive (fun j => q (e j)) (fun j => hq (e j)) =
      partitionTransitionMixture μ ν hμ hν p.eigenvalue p.positive q hq := by
    apply Subtype.ext
    simp only [partitionTransitionMixture,PositiveTraceClass.finiteMixture_val]
    exact e.sum_comp (fun j => (q j : ℂ) • (partitionTransitionOutput (μ j) ν (hμ j) hν p.eigenvalue p.positive).1)
  simpa only [he] using hh

end Cloning.TensorCloning
