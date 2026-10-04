import Cloning.YoungFlatCouplingLimit

/-! The exact physical flat coupling in arbitrary positive rank, with its
unconditional averaged crossing-dimension fidelity limit. -/
noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungFlatCoupling
open Cloning.YoungGeneral Cloning.TensorLie Cloning.YoungFlat
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def rankFlatCoupling (r : ℕ) (hr : 0<r) (N M : ℕ) : PMF (Shape r N × Shape r M) := by
  cases r with
  | zero => exact False.elim (Nat.not_lt_zero _ hr)
  | succ d => exact flatCoupling d N M

theorem rankFlatCoupling_map_fst (r : ℕ) (hr : 0<r) (N M : ℕ) :
    (rankFlatCoupling r hr N M).map Prod.fst = tensorFlatYoungPMF N r hr := by
  cases r with
  | zero => exact False.elim (Nat.not_lt_zero _ hr)
  | succ d => exact flatCoupling_map_fst d N M

theorem rankFlatCoupling_map_snd (r : ℕ) (hr : 0<r) (N M : ℕ) :
    (rankFlatCoupling r hr N M).map Prod.snd = tensorFlatYoungPMF M r hr := by
  cases r with
  | zero => exact False.elim (Nat.not_lt_zero _ hr)
  | succ d => exact flatCoupling_map_snd d N M

theorem rankFlatCoupling_incompatibleMass_tendsto (r : ℕ) (hr : 0<r) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ => (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun N => incompatibleMass r N (m N) (rankFlatCoupling r hr N (m N))) atTop (𝓝 0) := by
  cases r with
  | zero => exact False.elim (Nat.not_lt_zero _ hr)
  | succ d => exact flatCoupling_incompatibleMass_tendsto d m hm γ hγ hratio

/-- The coupling and its compatibility are constructed, so this scalar fidelity
limit contains no coupling or probability-of-compatibility premise. -/
theorem rankFlatCoupling_fidelity_tendsto (r k : ℕ) (hr : 0<r) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 1<γ)
    (hratio : Tendsto (fun N : ℕ => (m N : ℝ)/(N : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun N => coupledFlatFidelity r k N (m N) (rankFlatCoupling r hr N (m N))) atTop
      (𝓝 (γ ^ (-(((r*k : ℕ) : ℝ)/2)))) :=
  coupledFlatFidelity_tendsto_rpow r k hr m hm γ hγ hratio
    (fun N => rankFlatCoupling r hr N (m N))
    (fun N => rankFlatCoupling_map_fst r hr N (m N))
    (fun N => rankFlatCoupling_map_snd r hr N (m N))
    (rankFlatCoupling_incompatibleMass_tendsto r hr m hm γ hγ hratio)

end Cloning.YoungFlatCoupling
