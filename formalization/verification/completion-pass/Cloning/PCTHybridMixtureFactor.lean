import Cloning.PCTJointGaussianLaw
import Cloning.PCTJointGaussianWhitening
import Cloning.MixedChannelsPreparation
import Cloning.HybridCovariantization

/-! Exact classical–quantum factorization of the physical tangent mixture in
the genuine operator-valued L1 space. Independence is supplied by the proved
joint pushforward law, never as a hypothesis. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology BigOperators
namespace Cloning.PCTHybridMixture
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTGaussianOutput Cloning.PCTJointGaussianLaw
open Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.MultimodeCoherent
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k d : ℕ}

theorem hybridTranslation_prepare (h : Fin k → ℝ) (z : Fin d → ℂ)
    (f : (Fin k → ℝ) → ℝ) (hf : Integrable f) (X : TraceClass (Fock d)) :
    hybridTranslation (h,z) (prepareL1 f hf X) =
      classicalTranslation h (prepareL1 f hf (displacementTraceMap z X)) := by
  rw [hybridTranslation_apply, ← classicalTranslation_quantumL1Action_commute]
  congr 1
  exact (prepareL1_compLp (displacementTraceMap z) f hf X).symm

theorem integral_hybridTranslation_quantum (h : Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ) (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfone : ∫ x, f x = 1) (X : TraceClass (Fock d))
    (ν : Measure (Fin d → ℂ)) [IsFiniteMeasure ν] :
    (∫ z, hybridTranslation (h,z) (prepareL1 f hf X) ∂ν) =
      classicalTranslation h (prepareL1 f hf (∫ z, displacementTraceMap z X ∂ν)) := by
  simp_rw [hybridTranslation_prepare]
  let C : TraceClass (Fock d) →L[ℂ] HybridSpace k d :=
    (classicalTranslation h).toContinuousLinearMap.comp
      (QuantumToHybrid.prepare f hf hf0 hfone).map
  exact C.integral_comp_comm (integrable_displacement ν X)

theorem integrable_translated_pair {A : Type*} [Fintype A]
    (W : (A → ℝ) → (Fin k → ℝ)) (hW : Continuous W)
    (μ : Measure (A → ℝ)) [IsFiniteMeasure μ]
    (ν : Measure (Fin d → ℂ)) [IsFiniteMeasure ν] (X : HybridSpace k d) :
    Integrable (fun x : (A → ℝ) × (Fin d → ℂ) => hybridTranslation (W x.1,x.2) X)
      (μ.prod ν) := by
  apply (integrable_const ‖X‖).mono'
    ((continuous_hybridTranslation X).comp
      ((hW.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (norm_hybridTranslation (W x.1,x.2) X).le

variable {A : Type*} [Fintype A] [LinearOrder A] {s : ℕ}

/-- The full tangent average factors in actual hybrid L1: the classical
marginal averages translations of a fixed product of PCT thermal modes. -/
theorem tangent_hybrid_average_eq_classical_average
    (u : OrthonormalBasis (Fin (s + 1)) ℂ (Register (A × A)))
    (p : A → ℝ) (hp : ∀ a, 0 < p a)
    (hu : u 0 = coefficientVector (schmidtCoefficients p))
    (hgap : ∀ i j, i < j → 0 < p i - p j)
    (e : Fin d ≃ OrbitalPair A) (g : ℝ) (hg : 1 < g)
    (W : (A → ℝ) → (Fin k → ℝ)) (hW : Continuous W)
    (f : (Fin k → ℝ) → ℝ) (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfone : ∫ x, f x = 1) :
    let q : Fin d → ℝ := fun i => p (e i).1.2 / p (e i).1.1
    (∫ z, hybridTranslation (W (tangentClassical u p z), tangentDisplacement u p e z)
      (prepareL1 f hf (vectorMixture (numberBasis d) (productGeometric q)))
        ∂gaussianProductMeasure (fun _ : Fin s => g-1)) =
      ∫ h, classicalTranslation (W h) (prepareL1 f hf
        (vectorMixture (numberBasis d) (productGeometric (fun i => Thermal.pct g (q i)))))
          ∂classicalTangentLaw u p (g-1) := by
  dsimp only
  let q : Fin d → ℝ := fun i => p (e i).1.2 / p (e i).1.1
  let X := vectorMixture (numberBasis d) (productGeometric q)
  have hq0 (i : Fin d) : 0 < q i := div_pos (hp _) (hp _)
  have hq1 (i : Fin d) : q i < 1 :=
    (div_lt_one (hp _)).mpr (by linarith [hgap _ _ (e i).2])
  have hv : 0 < g-1 := sub_pos.mpr hg
  letI := classicalTangentLaw_probability u p hv
  letI := gaussianProductMeasure_probability (orbitalVariance_pos p hp hgap e hv)
  have havg := integral_jointTangent u p hp hu hgap e hv
    (fun x : (A → ℝ) × (Fin d → ℂ) =>
      hybridTranslation (W x.1,x.2) (prepareL1 f hf X))
    (integrable_translated_pair W hW _ _ _)
  change (∫ z, hybridTranslation (W (tangentClassical u p z), tangentDisplacement u p e z)
    (prepareL1 f hf X) ∂gaussianProductMeasure (fun _ : Fin s => g-1)) = _
  dsimp only [jointTangent] at havg
  rw [havg]
  simp_rw [integral_hybridTranslation_quantum _ f hf hf0 hfone X]
  have hb : orbitalVariance p e (g-1) = fun i => pctDisplacementVariance g (q i) := by
    funext i
    exact orbitalVariance_eq_pctDisplacementVariance g _ _ (hp _)
      (by linarith [hgap _ _ (e i).2])
  rw [hb, gaussian_displacement_productThermal_pct g hg hq0 hq1]

end Cloning.PCTHybridMixture
