import Cloning.PCTRankPurificationGeneralTheorem
import Cloning.PCTRankPurificationGeneralHaar
import Cloning.SampleRatioFinite

/-! A finite-copy squared-fidelity certificate for the fixed rank-bound
PCT channel, uniformly over every density whose actual rank is at most r. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ} [NeZero r]
local instance generalFiniteAmbientNeZero (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

theorem channel_rank_le_fidelity_sq_lower {s : ℕ} (k n t : ℕ)
    (hcard : Fintype.card (Fin (r+k)×Fin r)=s+1)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (ρ : Cloning.MatrixFidelity.State (Fin (r+k))) (hrank : ρ.matrix.rank≤r) :
    wernerScale n (n+t) s ≤
      ((tensorState ρ n).map
        (PCTRankGlobal.channel hcard n t (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toPositiveTracePreservingMap).rootFidelity
        (tensorState ρ (n+t))^2 := by
  have h := channel_rank_le_fidelity_lower k n t hcard b0 ρ hrank
  have hs := Real.sq_sqrt (wernerScale_pos n (n+t) s).le
  change Real.sqrt (wernerScale n (n+t) s)≤_ at h
  have hp := ((tensorState ρ n).map
    (PCTRankGlobal.channel hcard n t (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toPositiveTracePreservingMap).rootFidelity_nonneg
      (tensorState ρ (n+t))
  nlinarith [Real.sqrt_nonneg (wernerScale n (n+t) s)]

/-- Here s=rD−1 is supplied only by the exact cardinality identity. The
sample threshold and channel are independent of the input density. -/
theorem channel_rank_le_fidelity_sq_ge_target {s : ℕ} (k N M : ℕ)
    (hcard : Fintype.card (Fin (r+k)×Fin r)=s+1)
    (b0 : (Fin N → Fin (r+k))×(Fin N → Fin r))
    (ρ : Cloning.MatrixFidelity.State (Fin (r+k))) (hrank : ρ.matrix.rank≤r)
    (hN : 0<N) (hM : 0<M) (hs : 0<s)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (hR : SampleRatio.threshold s ε ≤ (N:ℝ)/M) :
    1-ε ≤
      ((tensorState ρ N).map
        (PCTRankGlobal.channel hcard N M (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toPositiveTracePreservingMap).rootFidelity
        (tensorState ρ (N+M))^2 :=
  (SampleRatio.wernerScale_ge_target N M s hN hM hs hε hε1 hR).trans
    (channel_rank_le_fidelity_sq_lower k N M hcard b0 ρ hrank)

end Cloning.PCTRankPurification
