import Cloning.YoungFlatCouplingQuantizer
import Cloning.YoungFlatCouplingConvergence
import Cloning.YoungFlatLimit
import Cloning.YoungFlatSupport
import Cloning.YoungFlatCompatibility
import Cloning.YoungFlatFidelity

/-! An actual exact-marginal coupling of two physical flat Young laws. -/
noncomputable section
open scoped BigOperators Topology Classical ENNReal
open MeasureTheory Filter
namespace Cloning.YoungFlatCoupling
open Cloning.YoungHyperplane Cloning.YoungGeneral Cloning.TensorLie Cloning.YoungFlat
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def independentPMF {I J : Type*} [Fintype I] [Fintype J] (p : PMF I) (q : PMF J) : PMF (I×J) :=
  completionPMF (fun i => (p i).toReal) (fun j => (q j).toReal) (fun _ _ => 0)
    (by simpa only [tsum_fintype, YoungCompatibility.probability] using
      (YoungCompatibility.hasSum_probability p).tsum_eq)
    (by simpa only [tsum_fintype, YoungCompatibility.probability] using
      (YoungCompatibility.hasSum_probability q).tsum_eq)
    (fun _ _ => le_rfl) (fun _ => by simp) (fun _ => by simp)

theorem independentPMF_map_fst {I J : Type*} [Fintype I] [Fintype J] (p : PMF I) (q : PMF J) :
    (independentPMF p q).map Prod.fst = p := by
  ext i
  exact (completionPMF_map_fst _ _ _ _ _ _ _ _ i).trans (ENNReal.ofReal_toReal (p.apply_ne_top i))

theorem independentPMF_map_snd {I J : Type*} [Fintype I] [Fintype J] (p : PMF I) (q : PMF J) :
    (independentPMF p q).map Prod.snd = q := by
  ext j
  exact (completionPMF_map_snd _ _ _ _ _ _ _ _ j).trans (ENNReal.ofReal_toReal (q.apply_ne_top j))

def positiveFlatCoupling (d N M : ℕ) (hN : 0<N) (hM : 0<M) :
    PMF (Shape (d+1) N × Shape (d+1) M) :=
  densityCoupling volume (sampleShape d N (flatSpectrum (d+1)))
    (sampleShape d M (flatSpectrum (d+1))) (flatDensity d N) (flatDensity d M)
    (measurable_sampleShape d N _) (measurable_sampleShape d M _)
    (integrable_flatDensity d N hN) (integrable_flatDensity d M hM)
    (flatDensity_nonneg d N) (flatDensity_nonneg d M)
    (integral_flatDensity d N hN) (integral_flatDensity d M hM)

theorem positiveFlatCoupling_map_fst (d N M : ℕ) (hN : 0<N) (hM : 0<M) :
    (positiveFlatCoupling d N M hN hM).map Prod.fst = tensorFlatYoungPMF N (d+1) (by omega) := by
  ext s
  exact (densityCoupling_map_fst _ _ _ _ _ _ _ _ _ _ _ _ _ s).trans
    (congrArg ENNReal.ofReal (densityBin_sampleShape d N hN (flatSpectrum (d+1))
      (fun _ => by unfold flatSpectrum; positivity) (flatSpectrum_sum _ (by omega)) s) |>.trans
      (ENNReal.ofReal_toReal (PMF.apply_ne_top _ s)))

theorem positiveFlatCoupling_map_snd (d N M : ℕ) (hN : 0<N) (hM : 0<M) :
    (positiveFlatCoupling d N M hN hM).map Prod.snd = tensorFlatYoungPMF M (d+1) (by omega) := by
  ext s
  exact (densityCoupling_map_snd _ _ _ _ _ _ _ _ _ _ _ _ _ s).trans
    (congrArg ENNReal.ofReal (densityBin_sampleShape d M hM (flatSpectrum (d+1))
      (fun _ => by unfold flatSpectrum; positivity) (flatSpectrum_sum _ (by omega)) s) |>.trans
      (ENNReal.ofReal_toReal (PMF.apply_ne_top _ s)))

/-- Exact physical coupling, with an independent completion at zero sample size. -/
def flatCoupling (d N M : ℕ) : PMF (Shape (d+1) N × Shape (d+1) M) :=
  if h : 0<N ∧ 0<M then positiveFlatCoupling d N M h.1 h.2
  else independentPMF (tensorFlatYoungPMF N (d+1) (by omega)) (tensorFlatYoungPMF M (d+1) (by omega))

theorem flatCoupling_eq_positive (d N M : ℕ) (hN : 0<N) (hM : 0<M) :
    flatCoupling d N M = positiveFlatCoupling d N M hN hM := by
  simp only [flatCoupling, dif_pos (And.intro hN hM)]

theorem flatCoupling_map_fst (d N M : ℕ) :
    (flatCoupling d N M).map Prod.fst = tensorFlatYoungPMF N (d+1) (by omega) := by
  unfold flatCoupling
  split_ifs with h
  · exact positiveFlatCoupling_map_fst d N M h.1 h.2
  · exact independentPMF_map_fst _ _

theorem flatCoupling_map_snd (d N M : ℕ) :
    (flatCoupling d N M).map Prod.snd = tensorFlatYoungPMF M (d+1) (by omega) := by
  unfold flatCoupling
  split_ifs with h
  · exact positiveFlatCoupling_map_snd d N M h.1 h.2
  · exact independentPMF_map_snd _ _

end Cloning.YoungFlatCoupling
