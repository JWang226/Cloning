import Cloning.InfiniteFiniteInstrument
import Cloning.InfiniteIsometricChannel

/-! Covariance of a finite rectangular instrument, with all dependent Hilbert
spaces kept abstract during the finite-sum algebra. -/
noncomputable section
open scoped BigOperators
namespace Cloning.TensorCloning
open Cloning.InfiniteTraceClass
set_option backward.isDefEq.respectTransparency false
variable {H K ι κ : Type*} {E : ι → Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [Fintype ι] [Fintype κ]

theorem finite_instrument_covariant
    (V : ∀ i, H →L[ℂ] E i) (Φ : ∀ i, κ → TraceClass (E i) →ₗ[ℂ] TraceClass K)
    (q : ι → κ → ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) (W : ∀ i, E i →L[ℂ] E i)
    (hin : ∀ i (A : TraceClass H), conjugationLinearMap (V i) (conjugationLinearMap S A) =
      conjugationLinearMap (W i) (conjugationLinearMap (V i) A))
    (hout : ∀ i j (A : TraceClass (E i)), Φ i j (conjugationLinearMap (W i) A) =
      conjugationLinearMap T (Φ i j A)) (A : TraceClass H) :
    (∑ i, ∑ j, q i j • Φ i j (conjugationLinearMap (V i) (conjugationLinearMap S A))) =
      conjugationLinearMap T (∑ i, ∑ j, q i j • Φ i j (conjugationLinearMap (V i) A)) := by
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hin i A, hout]

end Cloning.TensorCloning
