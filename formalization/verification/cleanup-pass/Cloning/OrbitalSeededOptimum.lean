import Cloning.Main
import Cloning.MultimodeThermalIdlerFidelity

/-! The concrete seeded Gaussian optimum at the manuscript's spectrum-dependent
parameters. This connects the operator theorem to `orbitalValue`; it does not
claim the universal displacement-covariant representation or quantum LAN. -/
noncomputable section
open scoped BigOperators
open Cloning Cloning.InfiniteTraceClass Cloning.InfiniteFidelity
namespace Cloning.OrbitalSeededOptimum

abbrev modeCount (d : ℕ) := Fintype.card (PairIndex d)

def modePair (d : ℕ) : Fin (modeCount d) ≃ PairIndex d :=
  (Fintype.equivFin (PairIndex d)).symm

def modeRatio {d : ℕ} (p : SimpleSpectrum d) (i : Fin (modeCount d)) : ℝ :=
  p.ratio (modePair d i)

theorem modeRatio_pos {d : ℕ} (p : SimpleSpectrum d) (i : Fin (modeCount d)) :
    0 < modeRatio p i := p.ratio_pos _

theorem modeRatio_lt_one {d : ℕ} (p : SimpleSpectrum d) (i : Fin (modeCount d)) :
    modeRatio p i < 1 := p.ratio_lt_one _

def targetState {d : ℕ} (p : SimpleSpectrum d) : DensityState (MultimodeIdler.Fock (modeCount d)) :=
  InfiniteDiagonalFidelity.productGeometricState (MultimodeIdler.numberBasis (modeCount d))
    (modeRatio p) (fun i => (modeRatio_pos p i).le) (modeRatio_lt_one p)

/-- The actual seeded map at the effective vacuum gain `g/(1-q_i)`. -/
def seededChannel {d : ℕ} (p : SimpleSpectrum d) (g : ℝ) (hg : 1 < g) :
    QuantumChannel (MultimodeIdler.Fock (modeCount d)) (MultimodeIdler.Fock (modeCount d)) :=
  MultimodeIdler.channel (fun i => Thermal.amplified g (modeRatio p i))
    (fun i => ((modeRatio_pos p i).trans (Thermal.lt_amplified hg (modeRatio_lt_one p i))).le)
    (fun i => Thermal.amplified_lt_one (by linarith) (modeRatio_lt_one p i))

def payoff {d : ℕ} (p : SimpleSpectrum d) (g : ℝ) (hg : 1 < g)
    (σ : DensityState (MultimodeIdler.Fock (modeCount d))) : ℝ :=
  stateFidelity ((seededChannel p g hg).toPositiveTracePreservingMap.mapState σ) (targetState p)

theorem thermal_product_eq_orbitalValue {d : ℕ} (p : SimpleSpectrum d) {g : ℝ} (hg : 1 < g) :
    (∏ i : Fin (modeCount d), Thermal.fidelity (modeRatio p i)
      (Thermal.amplified g (modeRatio p i))) = orbitalValue g p := by
  simp_rw [Thermal.fidelity_amplified_eq_modeFactor hg
    (modeRatio_pos p _).le (modeRatio_lt_one p _)]
  exact Fintype.prod_equiv (modePair d) _ _ (fun i => rfl)

/-- Exact attainment and upper bound over every joint idler density operator
at the original manuscript's pair ratios. No scalar-bound or moment premise. -/
theorem isGreatest_payoff {d : ℕ} (p : SimpleSpectrum d) {g : ℝ} (hg : 1 < g) :
    IsGreatest (Set.range (payoff p g hg)) (orbitalValue g p) := by
  have h := MultimodeThermalIdlerFidelity.isGreatest_idler_stateFidelity
    (modeRatio_pos p) (fun i => Thermal.lt_amplified hg (modeRatio_lt_one p i))
    (fun i => Thermal.amplified_lt_one (by linarith : 0 < g) (modeRatio_lt_one p i))
  rw [thermal_product_eq_orbitalValue p hg] at h
  exact h

theorem payoff_le_orbitalValue {d : ℕ} (p : SimpleSpectrum d) {g : ℝ} (hg : 1 < g)
    (σ : DensityState (MultimodeIdler.Fock (modeCount d))) : payoff p g hg σ ≤ orbitalValue g p :=
  (isGreatest_payoff p hg).2 ⟨σ, rfl⟩

end Cloning.OrbitalSeededOptimum
