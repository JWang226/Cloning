import Cloning.PCTProjectorPurityEnvelopeTheorem
import Cloning.PCTProjectorPurityEnvelopeRate
import Cloning.PCTPrescribedRankTheorem

/-! The literal liminf/limsup formulation, also for arbitrary requested output
sample sizes rather than only an explicit additional-copy count. -/
noncomputable section
open scoped Topology
open Filter
namespace Cloning.PCTProjectorPurity
open Cloning.PhysicalFlatGrassmann

/-- The full four-term inequality in the projector small-error proposition. -/
theorem physical_error_liminf_limsup (d k : ℕ) (P : Projector (d+1) k)
    (t : ℕ→ℕ) (δ : ℝ) (hδ : 0<δ) (hδr : δ<1/(2*((d+1:ℕ):ℝ)))
    (hgain : Tendsto (fun n=>((n+t n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) :
    lowerEnvelope ((d+1)*k) δ ≤
      liminf (fun n=>1-PhysicalFlatPCT.fidelity d k P n (t n)^2) atTop ∧
    liminf (fun n=>1-PhysicalFlatPCT.fidelity d k P n (t n)^2) atTop ≤
      limsup (fun n=>1-PhysicalFlatPCT.fidelity d k P n (t n)^2) atTop ∧
    limsup (fun n=>1-PhysicalFlatPCT.fidelity d k P n (t n)^2) atTop ≤
      upperEnvelope ((d+1)*k) (d*(d+2)) δ := by
  let E := fun n=>1-PhysicalFlatPCT.fidelity d k P n (t n)^2
  have hb (n : ℕ) : 0≤E n ∧ E n≤1 := by
    have h0 := PhysicalFlatPCT.fidelity_nonneg d k P n (t n)
    have h1 := PhysicalFlatPCT.fidelity_le_one d k P n (t n)
    dsimp [E]
    constructor <;> nlinarith [sq_nonneg (PhysicalFlatPCT.fidelity d k P n (t n))]
  have h := physical_error_envelopes d k t δ hδ hδr hgain
  refine ⟨?_,?_,?_⟩
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hh : lowerEnvelope ((d+1)*k) δ-ε≤liminf E atTop :=
      le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n=>(hb n).2))
        ((h ε hε).mono (fun n hn=>(hn P).1))
    linarith
  · exact liminf_le_limsup
      (isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n=>(hb n).2)))
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n=>(hb n).1)))
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n=>(hb n).1))
      ((h ε hε).mono (fun n hn=>(hn P).2))

/-- Arbitrary m(n)/n→1+δ, for the prescribed all-input channel. -/
theorem prescribed_error_liminf_limsup (d k : ℕ) (P : Projector (d+1) k)
    (m : ℕ→ℕ) (δ : ℝ) (hδ : 0<δ) (hδr : δ<1/(2*((d+1:ℕ):ℝ)))
    (hgain : Tendsto (fun n=>(m n:ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) :
    lowerEnvelope ((d+1)*k) δ ≤
      liminf (fun n=>1-PCTPrescribed.rankFidelity d k P n (m n)^2) atTop ∧
    liminf (fun n=>1-PCTPrescribed.rankFidelity d k P n (m n)^2) atTop ≤
      limsup (fun n=>1-PCTPrescribed.rankFidelity d k P n (m n)^2) atTop ∧
    limsup (fun n=>1-PCTPrescribed.rankFidelity d k P n (m n)^2) atTop ≤
      upperEnvelope ((d+1)*k) (d*(d+2)) δ := by
  have hg : 1<1+δ := by linarith
  have he := (PCTPrescribed.eventually_rankFidelity d k P m hg hgain).fun_comp
    (fun x:ℝ=>1-x^2)
  simp only [Function.comp_def] at he
  rw [← liminf_congr he,← limsup_congr he]
  exact physical_error_liminf_limsup d k P (fun n=>m n-n) δ hδ hδr
    (PCTPrescribed.addedCopies_ratio m hg hgain)

end Cloning.PCTProjectorPurity
