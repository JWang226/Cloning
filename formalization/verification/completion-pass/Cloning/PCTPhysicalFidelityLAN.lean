import Cloning.PCTPhysicalState
import Cloning.PCTTangentChartAdmissible
import Cloning.PCTHybridMixtureChannel

/-! The precise genuine mixed-LAN input required by physical PCT fidelity.
This file does not construct LAN channels. It derives moving-parameter LAN
from explicit compact-window estimates for the actual matrix experiment. -/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace ComplexOrder Topology Matrix.Norms.L2Operator
open MeasureTheory Filter NormedSpace Cloning.InfiniteTraceClass Cloning.Hybrid
namespace Cloning.PCTPhysicalFidelity
open Cloning.PCT Cloning.PCTReducedGaussian Cloning.PCTGaussianCovariance
open Cloning.PCTLocalChart Cloning.PCTJointGaussianWhitening
open Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {k d : ℕ}

abbrev Parameters (k : ℕ) := (Fin (k+1) → ℝ) × (PairIndex (k+1) → ℂ)

def reference (p : SimpleSpectrum (k+1)) (e : Fin d ≃ PairIndex (k+1)) : HybridPositive k d :=
  gaussianThermalPositive (fun _ : Fin k => 1/2) (fun _ => by norm_num)
    (fun i => p.ratio (e i)) (fun i => (p.ratio_pos (e i)).le) (fun i => p.ratio_lt_one (e i))

@[simp] theorem norm_reference (p : SimpleSpectrum (k+1)) (e : Fin d ≃ PairIndex (k+1)) :
    ‖(reference p e).1‖ = 1 := Cloning.MixedLANTransfer.norm_gaussianThermalPositive _ _ _ _ _

def parameterTranslation (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (θ : Parameters k) : (Fin k → ℝ) × (Fin d → ℂ) :=
  (whiten p.eigenvalue b θ.1, fun i => θ.2 (e i))

def model (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (θ : Parameters k) : HybridPositive k d :=
  (reference p e).map (translationChannel (parameterTranslation p b e θ))

@[simp] theorem model_val (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (θ : Parameters k) : (model p b e θ).1 =
      hybridTranslation (parameterTranslation p b e θ) (reference p e).1 := rfl

@[simp] theorem norm_model (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1))
    (θ : Parameters k) : ‖(model p b e θ).1‖ = 1 := by
  rw [model_val, norm_hybridTranslation, norm_reference]

theorem continuous_model (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1)) :
    Continuous (fun θ => (model p b e θ).1) := by
  apply (continuous_hybridTranslation (reference p e).1).comp
  exact ((continuous_whiten p.eigenvalue b).comp continuous_fst).prodMk (by fun_prop)

@[simp] theorem model_zero (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1)) :
    (model p b e 0).1 = (reference p e).1 := by
  rw [model_val]
  have he : parameterTranslation p b e 0 = 0 := by ext <;> simp [parameterTranslation, whiten]
  rw [he, hybridTranslation_zero]

def chartMatrix (p : SimpleSpectrum (k+1)) (θ : Parameters k) (L : ℕ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  exp (sampleScale L • orbitalGenerator p.eigenvalue θ.2) *
    Matrix.diagonal (fun i => ((p.eigenvalue i + sampleScale L * θ.1 i : ℝ) : ℂ)) *
    exp (-(sampleScale L • orbitalGenerator p.eigenvalue θ.2))

def chartTensor (p : SimpleSpectrum (k+1)) (θ : Parameters k) (L : ℕ) :
    TraceClass (Register (Fin L → Fin (k+1))) := matrixTensorPower (chartMatrix p θ L) L

/-- An explicit, currently unconstructed physical mixed-LAN hypothesis.
The same genuine channel sequences must work on every fixed compact window.
All comparison states, tensor matrices, scales and coordinates are literal. -/
structure CompactWindowLAN (p : SimpleSpectrum (k+1))
    (b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))) (e : Fin d ≃ PairIndex (k+1)) where
  forward : ∀ L, QuantumToHybrid (Register (Fin L → Fin (k+1))) (Fock d)
    (volume : Measure (Fin k → ℝ))
  reverse : ∀ L, HybridToQuantum (Fock d) (Register (Fin L → Fin (k+1)))
    (volume : Measure (Fin k → ℝ))
  approximation : ∀ K : Set (Parameters k), IsCompact K → (∀ θ ∈ K, ∑ i, θ.1 i = 0) →
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ L : ℕ in atTop, ∀ θ ∈ K,
      ‖(forward L).map (chartTensor p θ L) - (model p b e θ).1‖ ≤ ε L ∧
      ‖(reverse L).map (model p b e θ).1 - chartTensor p θ L‖ ≤ ε L

theorem CompactWindowLAN.moving_parameters
    {p : SimpleSpectrum (k+1)}
    {b : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1))} {e : Fin d ≃ PairIndex (k+1)}
    (lan : CompactWindowLAN p b e) (θ : ℕ → Parameters k) (θ₀ : Parameters k)
    (hθ : Tendsto θ atTop (𝓝 θ₀))
    (K : Set (Parameters k)) (hK : IsCompact K) (hzero : ∀ θ ∈ K, ∑ i, θ.1 i = 0)
    (hmem : ∀ᶠ L : ℕ in atTop, θ L ∈ K) :
    Tendsto (fun L => ‖(lan.forward L).map (chartTensor p (θ L) L) - (model p b e θ₀).1‖)
      atTop (𝓝 0) ∧
    Tendsto (fun L => ‖(lan.reverse L).map (model p b e θ₀).1 - chartTensor p (θ L) L‖)
      atTop (𝓝 0) := by
  obtain ⟨ε, hε, hbound⟩ := lan.approximation K hK hzero
  have hmodel : Tendsto (fun L => ‖(model p b e (θ L)).1 - (model p b e θ₀).1‖)
      atTop (𝓝 0) := by
    simpa using (((continuous_model p b e).tendsto θ₀).comp hθ |>.sub_const
      (model p b e θ₀).1).norm
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _)) _
      (by simpa using hε.add hmodel)
    filter_upwards [hmem, hbound] with L hL hb
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add (hb (θ L) hL).1 le_rfl)
  · apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _)) _
      (by simpa using (hmodel.const_mul 2).add hε)
    filter_upwards [hmem, hbound] with L hL hb
    calc
      _ ≤ ‖(lan.reverse L).map (model p b e θ₀).1 - (lan.reverse L).map (model p b e (θ L)).1‖ +
          ‖(lan.reverse L).map (model p b e (θ L)).1 - chartTensor p (θ L) L‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖(model p b e (θ L)).1 - (model p b e θ₀).1‖ + ε L := by
        apply add_le_add _ (hb (θ L) hL).2
        rw [← map_sub, norm_sub_rev (model p b e (θ L)).1 (model p b e θ₀).1]
        exact (lan.reverse L).norm_le_two _

end Cloning.PCTPhysicalFidelity
