import Cloning.PCTRankPurificationGeneralPhysical
import Cloning.PCTRankPurificationGeneralEmbedding

/-! One fixed rank-bound PCT channel satisfies the finite binomial guarantee
for every actual density of rank at most r. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
namespace Cloning.PCTRankPurification
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTRankAdapted Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {r : ℕ} [NeZero r]
local instance generalTheoremAmbientNeZero (k : ℕ) : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

theorem channel_rank_le_fidelity_lower {s : ℕ} (k n t : ℕ)
    (hcard : Fintype.card (Fin (r+k)×Fin r)=s+1)
    (b0 : (Fin n → Fin (r+k))×(Fin n → Fin r))
    (ρ : Cloning.MatrixFidelity.State (Fin (r+k))) (hrank : ρ.matrix.rank≤r) :
    Real.sqrt ((Nat.choose (n+s) s : ℝ) / Nat.choose (n+t+s) s) ≤
      ((tensorState ρ n).map
        (PCTRankGlobal.channel hcard n t (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toPositiveTracePreservingMap).rootFidelity
        (tensorState ρ (n+t)) := by
  obtain ⟨J,hJ,σ,rfl⟩ := exists_embedded_density r k ρ hrank
  have he : (tensorState (embeddedState J hJ σ) n).map
      (PCTRankGlobal.channel hcard n t (Cloning.TensorLie.coordinateInclusionMatrix r k) b0).toPositiveTracePreservingMap=
      embeddedPurificationOutput hcard J hJ σ n t := by
    apply Subtype.ext
    exact channel_embeddedState k n t hcard b0 J hJ σ
  rw [he]
  exact embeddedPurificationOutput_fidelity_lower hcard J hJ σ n t

end Cloning.PCTRankPurification
