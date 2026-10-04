import Cloning.YoungNormalization
import Cloning.YoungGeneralMoments
import Cloning.YoungGeneralFallback

/-!
# Concentration and dimension moments for the constructed Young law

These endpoints use the genuine normalized tableau PMF, constructed through
the RSK/Pieri proof. There is no PMF-existence or exact-law premise. Identifying
this law with a particular physical Schur measurement remains a separate
representation-theoretic statement.
-/

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace Cloning.YoungGeneral

def flatTableauPMF (r N : ℕ) (hr : 0 < r) : PMF (Shape r N) :=
  tableauPMF N (flatSpectrum r) (fun _ => by unfold flatSpectrum; positivity)
    (flatSpectrum_sum r hr)

theorem flatTableauPMF_toReal (r N : ℕ) (hr : 0 < r) (μ : Shape r N) :
    (flatTableauPMF r N hr μ).toReal = youngWeight N (flatSpectrum r) (fun i => (μ i).val) :=
  tableauPMF_toReal _ _ _ _ _

theorem flatTableauPMF_dimension_moments (r k : ℕ) (hr : 0 < r) :
    Tendsto (fun N => ∑ μ, (flatTableauPMF r N hr μ).toReal *
      normalizedDimension r k N μ) atTop (𝓝 1) ∧
    Tendsto (fun N => ∑ μ, (flatTableauPMF r N hr μ).toReal *
      inverseNormalizedDimension r k N μ) atTop (𝓝 1) :=
  dimension_moments_tendsto_one r k hr (fun N => flatTableauPMF r N hr)
    (fun N => flatTableauPMF_toReal r N hr)

open YoungCompatibility

theorem tableauPMF_fallback_errors {d : ℕ} (hd : 1 ≤ d)
    (K : Set (Fin (d + 1) → ℝ)) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, ∀ i, 0 < p i) (hanti : ∀ p ∈ K, StrictAnti p)
    (m : ℕ → ℤ) (γn : ℕ → ℝ) (γ : ℝ) (hγ : 1 < γ)
    (hγn : Tendsto γn atTop (𝓝 γ))
    (hm : ∀ n, (m n : ℝ) = γn n * (n : ℝ))
    (p : ℕ → Fin (d + 1) → ℝ) (hp : ∀ n, p n ∈ K)
    (hs : ∀ n, ∑ i, p n i = 1) (Q : ℕ → PMF (Fin (d + 1) → ℤ)) :
    let P := fun N => tableauPMF N (p N) (fun i => (hpos (p N) (hp N) i).le) (hs N)
    Tendsto (fun n => CountableScheffe.l1Distance
      (probability ((P n).bind (fun μ => fallbackKernel (γn n) n (m n) (integerShape μ))))
      (probability ((P n).bind (fun μ => rawKernel (γn n) (m n) (integerShape μ)))))
        atTop (𝓝 0) ∧
    Tendsto (fun n => |CountableScheffe.affinity
      (probability ((P n).bind (fun μ => fallbackKernel (γn n) n (m n) (integerShape μ))))
        (probability (Q n)) -
      CountableScheffe.affinity
        (probability ((P n).bind (fun μ => rawKernel (γn n) (m n) (integerShape μ))))
        (probability (Q n))|) atTop (𝓝 0) := by
  dsimp only
  apply tableau_fallback_errors_tendsto_zero hd K hK hpos hanti m γn γ hγ hγn hm p hp hs
  exact fun N => tableauPMF_toReal N (p N) _ (hs N)

end Cloning.YoungGeneral
