import Cloning.BosonicAmplifier
import Cloning.InfiniteKrausChannel
import Cloning.InfiniteOccupationStates

/-!
# The genuine one-mode amplifier channel on trace-class operators

The channel is the countable Kraus sum obtained by taking environment slices
of the explicitly constructed isometric dilation. Its definition acts linearly
on all trace-class operators, including off-diagonal input coherences.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Cloning.BosonicAmplifier

open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false

/-- The actual quantum-limited amplifier, in noise parameter `q=1-1/gain`. -/
def channel (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : QuantumChannel Fock Fock :=
  QuantumChannel.ofKraus (kraus q hq0 hq1) (kraus_norm_sq_hasSum q hq0 hq1)

/-- The defining Kraus series converges in the actual trace norm. -/
theorem channel_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A : TraceClass Fock) :
    HasSum (fun k => krausTerm (kraus q hq0 hq1 k) A) ((channel q hq0 hq1).toLinearMap A) :=
  QuantumChannel.ofKraus_hasSum _ _ A

/-- Scalar square-root amplitudes produce exactly their squared probability. -/
theorem vectorProjector_sqrt_smul {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : ℝ) (ha : 0 ≤ a) (x : H) :
    vectorProjector ((Real.sqrt a : ℂ) • x) = (a : ℂ) • vectorProjector x := by
  apply Subtype.ext
  ext y
  change ⟪(Real.sqrt a : ℂ) • x, y⟫_ℂ • ((Real.sqrt a : ℂ) • x) =
    (a : ℂ) • (⟪x, y⟫_ℂ • x)
  rw [inner_smul_left, smul_smul, smul_smul]
  have hs : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt ha
  congr 1
  simp only [Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) * ⟪x, y⟫_ℂ := by ring
    _ = _ := by rw [hs]

theorem krausTerm_numberProjector (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n k : ℕ) :
    krausTerm (kraus q hq0 hq1 k) (vectorProjector (numberBasis n)) =
      (weight q n k : ℂ) • vectorProjector (numberBasis (n + k)) := by
  rw [krausTerm_vectorProjector, kraus_numberBasis, vectorProjector_sqrt_smul]
  exact weight_nonneg hq0 hq1 n k

/-- Exact negative-binomial output of a number input under the actual channel. -/
theorem channel_numberProjector (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (channel q hq0 hq1).toLinearMap (vectorProjector (numberBasis n)) =
      vectorMixture (fun k => numberBasis (n + k)) (weight q n) := by
  have h := channel_hasSum q hq0 hq1 (vectorProjector (numberBasis n))
  simp only [krausTerm_numberProjector] at h
  exact h.tsum_eq.symm

end Cloning.BosonicAmplifier
