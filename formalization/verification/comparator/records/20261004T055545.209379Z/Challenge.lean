import Cloning.PhysicalCloningKnownTheorem
import Cloning.TensorCloningPrescribedLimits
import Cloning.SpectralAffineTheorem
import Cloning.PCTPrescribedFull
import Cloning.PCTPrescribedRankTheorem
import Cloning.PCTClosedForm
import Cloning.TensorSchurDecompositionSharpConcentration
import Cloning.MatrixLiftedChannel
import Cloning.TensorCloningLiftedFactorization
import Cloning.YoungPhysicalRounding
import Cloning.HybridGaussianScoreOptimum
import Cloning.PhysicalCloningConverseKnown
import Cloning.MixedLANTransfer
import Cloning.TensorPositiveSpectrumCompressionFidelity
import Cloning.PhysicalFlatConverseFinite
import Cloning.PBWSymmetricFrameRateGram
import Cloning.YoungUniformCharacterWindows
import Cloning.YoungUniformLocalPhysicalL1
import Cloning.YoungPhysicalRoundingUniformDensity
import Cloning.YoungPhysicalRoundingAffinity
import Cloning.HybridWeightedFidelityLimit
import Cloning.InfiniteAsymptoticCPCompactness
import Cloning.WeylSqueezerRepresentation
import Cloning.WeylDiagonalRepresentation
import Cloning.CovariantAmplifierLeastNoise
import Cloning.WernerPhysicalPullback
import Cloning.PCTProjectorPurityEnvelopeLimits

/-!
Independent statement comparator for the 27 named manuscript claims.
These declarations spell out mathematical types; none obtains its type from
an existing proof declaration, a type-of operation, or a theorem-type alias.
Project-specific mathematical definitions (physical channels, tensor states,
Schur sectors, priors, and fidelities) are shared with the audited library.
Consequently this is a project-relative statement comparison, not a
stock-Mathlib-only challenge such as the FLT comparator example.

The Challenge file intentionally leaves proofs as `sorry`; the separately
compiled Solution file uses the same declaration names and supplies proofs.
Neither file belongs to the All target or to the audited Cloning library.
Dimensions are explicit: full spectra use D=d+1; projector formulas use
rank r and ambient r+k. F denotes root fidelity unless explicitly squared.
-/
noncomputable section
open scoped BigOperators Topology Classical InnerProductSpace ComplexOrder Matrix Kronecker
open Filter MeasureTheory TopologicalSpace Cloning
open Cloning.PCT Cloning.InfiniteTraceClass Cloning.Hybrid Cloning.TensorLie
open Cloning.TensorCloning Cloning.PCTPhysicalState Cloning.PCTPhysicalFidelity
open Cloning.PCTJointGaussianWhitening Cloning.PhysicalCloningConverse
open Cloning.YoungGeneral Cloning.YoungHyperplane Cloning.YoungCompatibility Cloning.YoungRounding
open Cloning.MultimodeCoherent Cloning.TensorLAN Cloning.InfiniteFidelityHilbertSum
open Cloning.MultimodeCoherentGaussianMixture Cloning.ThermalWitness
namespace CloningVerification
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
instance comparatorWeightOccupationDecidableEq (D L : ℕ) (η : Fin D→ℤ) : DecidableEq (WeightOccupation D L η) := Classical.decEq _
instance comparatorTensorFiniteDimensional (n d : ℕ) : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- thm:known-optimum.  -/
theorem known_optimum {d : ℕ} (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    (∀ p : SimpleSpectrum (d+1),
      Tendsto (fun n => knownSpectrumValue n (m n) p) atTop (𝓝 (orbitalValue γ p))) ∧
    (∀ K : Set (SimpleSpectrum (d+1)), IsCompact K → ∀ ε>0,
      ∀ᶠ (n : ℕ) in atTop, ∀ p∈K, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        |spectrumPayoff n (m n) (prescribedKnownSpectrumChannel n (m n) (d+1)
          p.eigenvalue (fun a => (p.positive a).le) p.normalized) p U-orbitalValue γ p|<ε) := by
  sorry

/-- thm:unknown-optimum.  -/
theorem unknown_optimum {d : ℕ} (hd : 1≤d) (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    (∀ n M (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ), Uᴴ*U=1 →
      ∀ X : TraceClass (TensorRegister n (Fin (d+1))),
      (prescribedUniversalChannel n M d).toLinearMap (conjugationLinearMap (tensorOperator n U) X)=
        conjugationLinearMap (tensorOperator M U) ((prescribedUniversalChannel n M d).toLinearMap X)) ∧
    (∀ K : Set (SimpleSpectrum (d+1)), IsCompact K → ∀ ε>0,
      ∀ᶠ (n : ℕ) in atTop, ∀ p∈K, ∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
        |spectrumPayoff n (m n) (prescribedUniversalChannel n (m n) d) p U-universalValue γ p|<ε) ∧
    (∀ K : Set (SimpleSpectrum (d+1)), IsCompact K → K.Nonempty →
      closure (interior (SimpleSpectrum.toAffine '' K))=SimpleSpectrum.toAffine '' K →
      Tendsto (fun n => unknownSpectrumValue n (m n) K) atTop
        (𝓝 (⨅ p : K,universalValue γ p.val))) := by
  sorry

/-- thm:grassmann.  -/
theorem grassmann (r k : ℕ) (hr : 0<r) (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n => PhysicalFlatGrassmann.minimaxValue r k hr n (m n)) atTop
      (𝓝 (γ^(-(((r*k:ℕ):ℝ)/2)))) ∧
    (∀ ε>0, ∀ᶠ (n : ℕ) in atTop, ∀ P : PhysicalFlatGrassmann.Projector r k,
      |PhysicalFlatGrassmann.payoff r k hr n (m n) (prescribedRankFlatChannel r k hr n (m n)) P-
        γ^(-(((r*k:ℕ):ℝ)/2))|<ε) := by
  sorry

/-- thm:pct-comparison. Rank parameter in the second clause is r+1>1; ambient dimension is r+1+k. Includes the exact radical closed formula. -/
theorem pct_comparison {d : ℕ} (hd : 1≤d) (m : ℕ → ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 γ)) :
    (∀ (ρ : MatrixFidelity.State (Fin (d+1))) (hpos : ρ.matrix.PosDef)
      (hsimple : Function.Injective ρ.positive.isHermitian.eigenvalues),
      Tendsto (fun n => statePayoff n (m n) (PCTPrescribed.fullChannel d n (m n)) ρ) atTop
        (𝓝 (pctValue γ (densitySpectrum ρ hpos hsimple))) ∧
      pctValue γ (densitySpectrum ρ hpos hsimple)<universalValue γ (densitySpectrum ρ hpos hsimple)) ∧
    (∀ (r k : ℕ) (hr : 0<r) (P : PhysicalFlatGrassmann.Projector (r+1) k),
      limsup (fun n => PCTPrescribed.rankFidelity r k P n (m n)) atTop≤
        γ^(-((((r+1)*k:ℕ):ℝ)/2))*(Real.sqrt (2*γ-1)/γ)^((((r+1:ℕ):ℝ)-1)/2) ∧
      limsup (fun n => PCTPrescribed.rankFidelity r k P n (m n)) atTop<
        γ^(-((((r+1)*k:ℕ):ℝ)/2))) ∧
    (∀ p : SimpleSpectrum (d+1),
      pctValue γ p=(Real.sqrt (2*γ-1)/γ)^((((d+1:ℕ):ℝ)-1)/2)*
        ∏ ij : PairIndex (d+1),
          (Real.sqrt (γ+(γ-1)*p.ratio ij)+Real.sqrt (p.ratio ij*(γ-1+γ*p.ratio ij)))/
            (γ*(1+p.ratio ij))) := by
  sorry

/-- lem:young-concentration.  -/
theorem young_concentration (D : ℕ) :
    ∃ N₀ : ℕ, ∀ N≥N₀, ∀ (p : Fin D→ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1),
      Antitone p → tailProbability (tensorYoungPMF N D p hp hs) p (shrinkingRadius N)≤
        Real.exp (-((N:ℝ)^(1/3:ℝ))/4) := by
  sorry

/-- prop:lifted-kernel-bound. Exact scalar block sum for arbitrary finite lifts and actual physical stochastic Schur-copy kernels. Physical channel action, sector orthogonality and homogeneity are discharged; no action premise is assumed. -/
theorem lifted_kernel_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {α : I→Type*} {β κ : J→Type*}
    [∀ i,Fintype (α i)] [∀ j,Fintype (β j)] [∀ j,Fintype (κ j)]
    [∀ i,DecidableEq (α i)] [∀ j,DecidableEq (β j)] [∀ j,DecidableEq (κ j)]
    (T : ∀ i j,Channels.MatrixChannel (α i) (β j))
    (ρ : ∀ i,MatrixFidelity.State (α i)) (σ : ∀ j,MatrixFidelity.State (β j))
    (τ : ∀ j,MatrixFidelity.State (κ j))
    (w : I→J→ℝ) (hw : ∀ i j,0≤w i j) (p : J→ℝ) (hp : ∀ j,0≤p j) :
    MatrixFidelity.fidelity (MatrixLiftedChannel.liftedOutput T ρ τ w)
      (Matrix.blockDiagonal' (fun j => (p j • (σ j).matrix) ⊗ₖ (τ j).matrix))=
      ∑ j,Real.sqrt (p j)*MatrixFidelity.fidelity
        (MatrixLiftedChannel.transitionOutput T ρ w j) (σ j).matrix ∧
    (∀ (d n m : ℕ) (p : SimpleSpectrum (d+1))
      (U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ))
      (q : SchurCopy n (d+1)→SchurCopy m (d+1)→ℝ)
      (hq : ∀ i j,0≤q i j) (hs : ∀ i,∑ j,q i j=1),
      let w := kernelJointWeight n m (d+1) p.eigenvalue q
      let hw := kernelJointWeight_nonneg n m (d+1) p.eigenvalue q hq
      spectrumPayoff n m (TensorCloning.channel n m (d+1) q hq hs) p U=
        ∑ j : SchurCopy m (d+1),Real.sqrt (knownCopyWeight m (d+1) p.eigenvalue j)*
          (copyOutputBlock n m (d+1) p.eigenvalue p.positive U w hw j).rootFidelity
            (copySectorState ((recursivePhysicalDecomposition m (d+1)).get j) U p.eigenvalue p.positive)) := by
  sorry

/-- prop:sector-fidelity. Single-sector fidelity is the t=1 unit-mass specialization; target signed lattice admissibility is concluded. -/
theorem sector_fidelity {D : ℕ} (K : Set (SimpleSpectrum D)) (hK : IsCompact K)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ) (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ→ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (∀ ε>0, ∀ᶠ (n : ℕ) in atTop, ∀ p∈K, ∀ t : ℕ,
      ∀ (μ : Fin t→Fin D→ℕ) (ν : Fin D→ℕ) (hμ : ∀ i,Antitone (μ i)) (hν : Antitone ν),
      (∀ i a,|(μ i a:ℝ)/n-p.eigenvalue a|≤δ n) →
      (∀ a,|(ν a:ℝ)/(m n:ℝ)-p.eigenvalue a|≤δ n) →
      ∀ (w : Fin t→ℝ) (hw : ∀ i,0≤w i), (∑ i,w i)=1 →
      |(partitionTransitionMixture μ ν hμ hν p.eigenvalue p.positive w hw).rootFidelity
        (partitionGibbsPositive ν hν p.eigenvalue p.positive)-orbitalValue γ p|<ε) ∧
    (∀ᶠ (n : ℕ) in atTop, ∀ p∈K, ∀ μ ν : Fin D→ℤ,
      IsYoung (n:ℤ) μ → (∑ a,ν a)=(m n:ℤ) →
      (∀ a,|(μ a:ℝ)/n-p.eigenvalue a|≤δ n) →
      (∀ a,|(ν a:ℝ)/(m n:ℝ)-p.eigenvalue a|≤δ n) →
      Compatible (n:ℤ) (m n:ℤ) μ ν ∧ IsYoung (m n:ℤ) ν) := by
  sorry

/-- prop:young-rounding.  -/
theorem young_rounding {d : ℕ} (hd : 1≤d) :
    (∀ (n m : ℤ) (μ : Fin (d+1)→ℤ) (g : ℝ), 0≤g → (∑ i,μ i)=n → (m:ℝ)=g*(n:ℝ) →
      ∀ z,roundingPMF g (fun i => (μ i.castSucc:ℝ)) z≠0 →
      ∀ i,|(complete m z i:ℝ)-g*(μ i:ℝ)|≤(d:ℝ)*((g+1)/2)) ∧
    (∀ (m : ℕ→ℤ) (g δ : ℕ→ℝ) (γ a : ℝ), 0<a → 1<γ →
      Tendsto g atTop (𝓝 γ) → Tendsto δ atTop (𝓝 0) →
      (∀ n,(m n:ℝ)=g n*(n:ℝ)) →
      ∀ᶠ (n : ℕ) in atTop, ∀ p : Fin (d+1)→ℝ,
        (∀ i,a≤p i) → (∀ i j,i<j → a≤p i-p j) →
        ∀ μ : Fin (d+1)→ℤ, (∑ i,μ i)=(n:ℤ) →
        (∀ i,|(μ i:ℝ)-(n:ℝ)*p i|≤(n:ℝ)*δ n) →
        ∀ z,roundingPMF (g n) (fun i => (μ i.castSucc:ℝ)) z≠0 →
          Compatible (n:ℤ) (m n) μ (complete (m n) z)) ∧
    (∀ (K : Set (Fin (d+1)→ℝ)) (hK : IsCompact K)
      (hp : ∀ p∈K,∑ i,p i=1) (hp0 : ∀ p∈K,∀ i,0<p i),
      (∀ p∈K,StrictAnti p) → ∀ (m : ℕ→ℕ), Tendsto m atTop atTop →
      ∀ γ : ℝ, 1<γ → Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ) → ∀ ε>0,
      ∃ N₀ : ℕ,∀ N≥N₀,∀ (p : Fin (d+1)→ℝ) (hpK : p∈K),
        |CountableScheffe.affinity
          (probability (tensorYoungFallbackOutput d N (m N) ((m N:ℝ)/N) p
            (fun i => (hp0 p hpK i).le) (hp p hpK)))
          (probability (tensorYoungIntegerPMF d (m N) p (fun i => (hp0 p hpK i).le) (hp p hpK)))-
          classicalValue γ (d+1)|<ε) := by
  sorry

/-- lem:lifted-fidelity-factorization.  -/
theorem lifted_fidelity_factorization {d : ℕ} (K : Set (SimpleSpectrum (d+1))) (hK : IsCompact K)
    (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ) (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ))
    (δ : ℕ→ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (q : ∀ n,SimpleSpectrum (d+1)→SchurCopy n (d+1)→SchurCopy (m n) (d+1)→ℝ)
    (hq : ∀ n p i j,0≤q n p i j) (hs : ∀ n p i,∑ j,q n p i j=1)
    (hbad : ∀ η>0,∀ᶠ (n : ℕ) in atTop,∀ p∈K,
      kernelBadMass n (m n) (d+1) p.eigenvalue (δ n) (q n p)<η) :
    ∀ ε>0,∀ᶠ (n : ℕ) in atTop,∀ p∈K,∀ U : unitary (Matrix (Fin (d+1)) (Fin (d+1)) ℂ),
      |spectrumPayoff n (m n) (TensorCloning.channel n (m n) (d+1) (q n p) (hq n p) (hs n p)) p U-
        orbitalValue γ p*kernelAffinity n (m n) (d+1) p.eigenvalue (q n p)|<ε := by
  sorry

/-- thm:gaussian-amplification. First clause includes k=0 orbital model and all real radii. Second uses the exact physical score polytope, with normalized measure cancellation proved in ScoreReferenceMeasure. -/
theorem gaussian_amplification {k s : ℕ} (γ : ℝ) (hγ : 1<γ) :
    (∀ (B : PhaseBody k s) (a : Fin k→ℝ) (ha : ∀ i,0<a i)
      (q : Fin s→ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1),
      Tendsto (B.optimalPayoff (Real.sqrt γ)
        (gaussianThermalPositive a ha q hq0 hq1) (gaussianThermalPositive a ha q hq0 hq1)) atTop
        (𝓝 (Thermal.classicalBase γ^((k:ℝ)/2)*∏ i,Thermal.modeFactor γ (q i)))) ∧
    (∀ (p : SimpleSpectrum (k+1))
      (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
      (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s≃PairIndex (k+1)),
      Tendsto (scoreGaussianOptimal p b hb e γ) atTop (𝓝 (universalValue γ p))) := by
  sorry

/-- thm:LAN-full. Explicit channel errors are stated. Target c_n=sampleRatio n (m n), c0=sqrt γ follows from sampleRatio_tendsto; statement is stronger for arbitrary convergent scales. -/
theorem lan_full {k s : ℕ} (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s≃PairIndex (k+1)) :
    ∃ lan : CompactWindowLAN p b e,
      (∀ K : Set (PCTPhysicalFidelity.Parameters k),IsCompact K → (∀ θ∈K,∑ i,θ.1 i=0) →
        ∃ ε : ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ (n : ℕ) in atTop,∀ θ∈K,
          ‖(lan.forward n).map (chartTensor p θ n)-(model p b e θ).1‖≤ε n ∧
          ‖(lan.reverse n).map (model p b e θ).1-chartTensor p θ n‖≤ε n) ∧
      (∀ (m : ℕ→ℕ),Tendsto m atTop atTop → ∀ (c : ℕ→ℝ) (c₀ : ℝ),
        Tendsto c atTop (𝓝 c₀) → ∀ K : Set (PCTPhysicalFidelity.Parameters k),
        IsCompact K → (∀ θ∈K,∑ i,θ.1 i=0) →
        ∃ δ η : ℕ→ℝ,Tendsto δ atTop (𝓝 0) ∧ Tendsto η atTop (𝓝 0) ∧
          ∀ᶠ (n : ℕ) in atTop,∀ θ∈K,
            ‖(lan.reverse n).map (model p b e θ).1-chartTensor p θ n‖≤δ n ∧
            ‖(lan.forward (m n)).map (chartTensor p (c n • θ) (m n))-
              (model p b e (c₀ • θ)).1‖≤η n) := by
  sorry

/-- cor:LAN-orb. Identity output scaling supplies forward-input errors; the constructed lan is selected before all windows and output sequences. -/
theorem lan_orbital {k s : ℕ} (p : SimpleSpectrum (k+1))
    (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
    (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s≃PairIndex (k+1)) :
    ∃ lan : CompactWindowLAN p b e,
      ∀ (m : ℕ→ℕ) (γ : ℝ),0<γ → Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ) →
      ∀ L : ℕ, ∃ δ η : ℕ→ℝ,Tendsto δ atTop (𝓝 0) ∧ Tendsto η atTop (𝓝 0) ∧
        ∀ᶠ (n : ℕ) in atTop,∀ ξ∈Hybrid.phaseSpaceBox 0 s ((L:ℝ)+1),
          let U := localUnitary p (orbitalParameters e ξ) n
          ‖(removeClassicalReverse (lan.reverse n)).map
              (translatedPositive ξ (orbitalReference p e)).1-(tensorState (orbitState p U) n).1‖≤δ n ∧
          ‖(removeClassicalForward (lan.forward (m n))).map
              (tensorState (orbitState p U) (m n)).1-
              (translatedPositive (Real.sqrt γ • ξ) (orbitalReference p e)).1‖≤η n := by
  sorry

/-- lem:LAN-fidelity-transfer.  -/
theorem lan_fidelity_transfer {Ω A B G H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : HybridToQuantum G A μ) (M : QuantumChannel A B) (T : QuantumToHybrid B H μ)
    (ρ : PositiveTraceClass A) (σ : PositiveTraceClass B) (Φ : PositiveL1 G μ) (Ψ : PositiveL1 H μ)
    (hσ : ‖σ.1‖=1) (hΦ : ‖Φ.1‖=1) (δ η : ℝ)
    (hδ : ‖S.map Φ.1-ρ.1‖≤δ) (hη : ‖T.map σ.1-Ψ.1‖≤η) :
    (ρ.map M.toPositiveTracePreservingMap).rootFidelity σ≤
      (Φ.map (MixedLANTransfer.transferred S M T)).rootFidelity Ψ+Real.sqrt δ+Real.sqrt η := by
  sorry

/-- lem:exact-compression. Target partition is μ+ω. Nonnegative spectra strengthen positive-spectrum claim; trace-zero density convention at a zero partition function is explicit in the underlying definition. -/
theorem exact_compression {r : ℕ} (μ ω : Fin r→ℕ) (hμ : Antitone μ) (hω : Antitone ω) (k : ℕ) :
    (∀ (p : Fin r→ℝ) (hp : ∀ a,0≤p a),
      sectorGibbsDensity
        (partitionHighestTensor (padPartition μ k) (padPartition_antitone μ hμ k))
        (padPartition μ k) (partitionHighestTensor_cartan _ _) (partitionHighestTensor_raising_zero _ _)
        (padSpectrum p k)=
      conjugationLinearMap (rankSectorEmbedding μ hμ k).toContinuousLinearMap
        (sectorGibbsDensity (partitionHighestTensor μ hμ) μ
          (partitionHighestTensor_cartan μ hμ) (partitionHighestTensor_raising_zero μ hμ) p)) ∧
    (∀ X : Matrix (PartitionIndex μ hμ) (PartitionIndex μ hμ) ℂ,
      let Jμ := rankSectorEmbeddingMatrix μ hμ k
      let Jν := rankSumSectorEmbeddingMatrix μ ω hμ hω k
      (Jν*Jνᴴ)*((physicalCartanMatrixChannel (padPartition μ k) (padPartition ω k)
        (padPartition_antitone μ hμ k) (padPartition_antitone ω hω k)).toFun (Jμ*X*Jμᴴ))*(Jν*Jνᴴ)=
        rankCartanRatio μ ω hμ hω k • (Jν*(physicalCartanMatrixChannel μ ω hμ hω).toFun X*Jνᴴ)) ∧
    (∀ (p : Fin r→ℝ) (hp : ∀ a,0≤p a),
      nonnegativeCartanGibbsFidelity (padPartition μ k) (padPartition ω k)
        (padPartition_antitone μ hμ k) (padPartition_antitone ω hω k)
        (padSpectrum p k) (padSpectrum_nonneg p hp k)=
      Real.sqrt (YoungDimensionRatio.dimensionRatio r k (fun a => (μ a:ℝ))/
        YoungDimensionRatio.dimensionRatio r k (fun a => ((μ a+ω a:ℕ):ℝ)))*
        nonnegativeCartanGibbsFidelity μ ω hμ hω p hp) := by
  sorry

/-- prop:grassmann-finite-converse. flatConverseBound is the literal square root of the product of physical Young dimension-ratio moments. The result holds even without n≤m. -/
theorem grassmann_finite_converse (r k : ℕ) (hr : 0<r) (n m : ℕ) :
    PhysicalFlatGrassmann.minimaxValue r k hr n m≤PhysicalFlatConverse.flatConverseBound r k hr n m := by
  sorry

/-- lem:PBW-fixed-height. η denotes actual lowering weight with this sign convention; the height is ∑a a*ηa. Root-gap upper bounds are unnecessary. -/
theorem pbw_fixed_height {D : ℕ} (L : ℕ) (c : ℝ) (hc : 0<c) :
    (∃ C : ℝ,0≤C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (μ : Fin D→ℕ) (hμ : Antitone μ),
      (∀ a : PositiveRoot D,c*(N:ℝ)≤rootGap μ a) → ∀ η : Fin D→ℤ,
      IsUnit (Matrix.gram ℂ (weightRawFrame μ hμ L η)) ∧
      ∀ i j : WeightOccupation D L η,
        ‖⟪weightRawFrame μ hμ L η i,weightRawFrame μ hμ L η j⟫_ℂ-
          (if i=j then 1 else 0:ℂ)‖≤C/Real.sqrt (N:ℝ)) ∧
    (∃ C : ℝ,0≤C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (μ : Fin D→ℕ) (hμ : Antitone μ),
      (∀ a : PositiveRoot D,c*(N:ℝ)≤rootGap μ a) →
      ∀ η : Fin D→ℤ,(∑ a,(a.val:ℤ)*η a≤(L:ℤ)) →
      ∃ b : OrthonormalBasis (WeightOccupation D L η) ℂ
        ↥(cyclicSector (partitionHighestTensor μ hμ) ⊓ cartanWeightSpace (∑ a,μ a) μ η),
        (∀ i,(b i : TensorRegister (∑ a,μ a) (Fin D))=weightSymmetricFrame μ hμ L η i) ∧
        ∀ i,‖weightSymmetricFrame μ hμ L η i-weightRawFrame μ hμ L η i‖≤C/Real.sqrt (N:ℝ)) := by
  sorry

/-- lem:uniform-character-normalization. Numerator is p^μ, denominator the actual character; no reciprocal reversal. Partition total-size restriction is unnecessary. -/
theorem character_normalization {D : ℕ} (K : Set (SimpleSpectrum D)) (hK : IsCompact K)
    (δ : ℕ→ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε>0,∀ᶠ N : ℕ in atTop,∀ p∈K,∀ μ : Fin D→ℕ,Antitone μ →
      (∀ i,|(μ i:ℝ)/(N:ℝ)-p.eigenvalue i|≤δ N) →
      |(∏ i,p.eigenvalue i^μ i)/physicalSectorCharacter μ p.eigenvalue-
        spectralCorrection p.eigenvalue|<ε := by
  sorry

/-- lem:young-local-limit.  -/
theorem young_local_limit (d : ℕ) (K : Set (Fin (d+1)→ℝ)) (hK : IsCompact K)
    (hp : ∀ p∈K,∑ i,p i=1) (hp0 : ∀ p∈K,∀ i,0<p i) (hord : ∀ p∈K,StrictAnti p) :
    ∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,∀ (p : Fin (d+1)→ℝ) (hpK : p∈K),
      (∫ x,|tensorYoungDensity d N p (fun i => (hp0 p hpK i).le) (hp p hpK) x-
        covarianceGaussian d p (hp p hpK) x|)<ε := by
  sorry

/-- lem:randomized-dilation.  -/
theorem randomized_dilation (d : ℕ) (K : Set (Fin (d+1)→ℝ)) (hK : IsCompact K)
    (hp : ∀ p∈K,∑ i,p i=1) (hp0 : ∀ p∈K,∀ i,0<p i) (hord : ∀ p∈K,StrictAnti p)
    (m : ℕ→ℕ) (hm : Tendsto m atTop atTop) (γ : ℝ) (hγ : 0<γ)
    (hratio : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    (∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,∀ (p : Fin (d+1)→ℝ) (hpK : p∈K),
      (∫ x,|roundedDensity (Real.sqrt (m N:ℝ))⁻¹ (headAnchor d (m N) p) ((m N:ℝ)/N)
          (tensorYoungHeadPMF d N p (fun i => (hp0 p hpK i).le) (hp p hpK)) x-
        affineDensity (Real.sqrt γ) 0 (headGaussian d p (hp p hpK)) x|)<ε) ∧
    (∀ ε>0,∃ N₀ : ℕ,∀ N≥N₀,∀ (p : Fin (d+1)→ℝ) (hpK : p∈K),
      |CountableScheffe.affinity
        (probability (tensorYoungRawOutput d N (m N) ((m N:ℝ)/N) p
          (fun i => (hp0 p hpK i).le) (hp p hpK)))
        (probability (tensorYoungIntegerPMF d (m N) p (fun i => (hp0 p hpK i).le) (hp p hpK)))-
        classicalValue γ (d+1)|<ε) := by
  sorry

/-- lem:weighted-fidelity. Finite regularized inverse limit, not an assumed uniform bound; target T is arbitrary positive trace class including zero. Bounded weight need not be injective. -/
theorem weighted_fidelity {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace Ω] (μ : Measure Ω) :
    (∀ (A B W : H→L[ℂ] H) (hA : 0≤A) (hB : 0≤B) (hW : 0≤W)
      (hTA : IsTraceClass A) (hTB : IsTraceClass B) (M : ℝ),
      Tendsto (fun ε : ℝ =>
        (trace (B*CFC.rpow (InfiniteFidelity.regularizedWeight W ε) (-1))
          (isTraceClass_mul_mul (A:=1)
            (B:=CFC.rpow (InfiniteFidelity.regularizedWeight W ε) (-1)) hTB)).re)
        (𝓝[>] (0:ℝ)) (𝓝 M) →
      InfiniteFidelity.fidelity A B hA hB hTA hTB^2≤
        (trace (A*W) (isTraceClass_mul_mul (A:=1) (B:=W) hTA)).re*M) ∧
    (∀ (R : PositiveField (H:=H) μ) (g : Ω→ℝ) (hg : Integrable g μ)
      (hgn : ∀ x,0≤g x) (T : PositiveTraceClass H) (W : H→L[ℂ] H),0≤W →
      ∀ M : ℝ,Tendsto (regularizedInverseMoment T W) (𝓝[>] (0:ℝ)) (𝓝 M) →
      ∀ χ : Ω→ℝ,(∀ x,0<χ x) →
      Integrable (fun x => χ x*witnessMoment (R.value x).1 W) μ →
      Integrable (fun x => g x/χ x) μ →
      R.rootFidelity (PositiveField.productPositive g hg hgn T)^2≤
        (∫ x,χ x*witnessMoment (R.value x).1 W ∂μ)*(∫ x,g x/χ x ∂μ)*M) := by
  sorry

/-- lem:compact-cp-limit.  -/
theorem compact_cp_limit {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [SeparableSpace K]
    (L : ℕ→TraceClass H→L[ℂ] TraceClass K) (M c : ℝ)
    (hb : ∀ n,‖L n‖≤M) (hcp : ∀ n,IsCompletelyPositive (L n).toLinearMap)
    (htrace : ∀ A,0≤A.1 → limsup (fun n => (traceCLM (L n A)).re) atTop≤c*(traceCLM A).re)
    (U : G→H→L[ℂ] H) (V : G→K→L[ℂ] K)
    (hcov : ∀ g A,Tendsto (fun n => ‖L n (sandwichCLM (U g) (star (U g)) A)-
      sandwichCLM (V g) (star (V g)) (L n A)‖) atTop (𝓝 (0:ℝ))) :
    ∃ Ψ : TraceClass H→ₗ[ℂ] TraceClass K,
      IsCompletelyPositive Ψ ∧
      (∀ A,0≤A.1 → (traceCLM (Ψ A)).re≤c*(traceCLM A).re) ∧
      (∀ g A,Ψ (sandwichCLM (U g) (star (U g)) A)=sandwichCLM (V g) (star (V g)) (Ψ A)) ∧
      ∃ φ : ℕ→ℕ,StrictMono φ ∧
        (∀ A x y,Tendsto (fun n => ⟪x,(L (φ n) A).1 y⟫_ℂ) atTop (𝓝 ⟪x,(Ψ A).1 y⟫_ℂ)) ∧
        (∀ A (O : K→L[ℂ] K),IsCompactOperator O →
          Tendsto (fun n => tracePairing (L (φ n) A) O) atTop (𝓝 (tracePairing (Ψ A) O))) := by
  sorry

/-- lem:covariant-amplifier-representation.  -/
theorem covariant_amplifier_representation {D : ℕ} (Φ : QuantumChannel (Fock D) (Fock D))
    (G : Fin D→ℝ) (hG : ∀ i,1<G i)
    (hcov : ∀ a T,Φ.toLinearMap (displacementTraceMap a T)=
      displacementTraceMap (diagonalScale (diagonalGainAmplitude G) a) (Φ.toLinearMap T)) :
    (∃ σ : DensityState (Fock D),Φ.toLinearMap=
      (WeylSqueezer.channel (diagonalGainAmplitude G) (diagonalNoiseAmplitude G)
        (WeylSqueezer.gain_hyperbolic G (fun i => (hG i).le)) σ).toLinearMap) ∧
    (∃! σ : TraceClass (Fock D),0≤σ.1 ∧ traceCLM σ=1 ∧
      ∀ a,diagonalWeylMultiplier Φ.heisenberg (diagonalGainAmplitude G) a=
        tracePairing σ (displacement (diagonalScale (diagonalNoiseAmplitude G) (star a)))) := by
  sorry

/-- prop:least-noise-moment.  -/
theorem least_noise_moment {D : ℕ} (Γ : TraceClass (Fock D)→ₗ[ℂ] TraceClass (Fock D))
    (hCP : IsCompletelyPositive Γ)
    (htrace : ∀ A,0≤A.1 → (traceCLM (Γ A)).re≤(traceCLM A).re)
    (γ : ℝ) (hγ : 1<γ)
    (hΓ : ∀ a A,Γ (displacementTraceMap a A)=displacementTraceMap (Real.sqrt γ • a) (Γ A))
    (q : Fin D→ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1)
    (w : Fin D→ℕ→ℝ) (hw0 : ∀ i n,0≤w i n) (hw : ∀ i,Antitone (w i)) :
    (tracePairing (Γ (vectorMixture (numberBasis D) (productGeometric q)))
      (MultimodeLeastNoise.productObservable w hw0 hw)).re≤
      (traceCLM (Γ (vectorMixture (numberBasis D) (productGeometric q)))).re*
        (tracePairing (vectorMixture (numberBasis D)
          (productGeometric (fun i => Thermal.amplified γ (q i))))
            (MultimodeLeastNoise.productObservable w hw0 hw)).re := by
  sorry

/-- prop:flat-prior-converse.  -/
theorem flat_prior_converse {k s : ℕ} (γ : ℝ) (hγ : 1<γ) :
    (∀ (B : PhaseBody k s) (a : Fin k→ℝ) (ha : ∀ i,0<a i)
      (q : Fin s→ℝ) (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i<1),
      ∀ ε>0,∀ᶠ L : ℝ in atTop,∀ Λ : HybridChannel k s,
        B.payoff (Real.sqrt γ) Λ (gaussianThermalPositive a ha q hq0 hq1)
          (gaussianThermalPositive a ha q hq0 hq1) L≤
          Thermal.classicalBase γ^((k:ℝ)/2)*(∏ i,Thermal.modeFactor γ (q i))+ε) ∧
    (∀ (p : SimpleSpectrum (k+1))
      (b : OrthonormalBasis (Fin (k+1)) ℝ (EuclideanSpace ℝ (Fin (k+1))))
      (hb : b 0=sqrtSpectrum p.eigenvalue) (e : Fin s≃PairIndex (k+1)),
      limsup (scoreGaussianOptimal p b hb e γ) atTop≤universalValue γ p) := by
  sorry

/-- lem:Werner-Fock. Physical dimension is s+1≥2. Exact coefficient/occupation identification and trace-norm convergence, not just weak convergence. -/
theorem werner_fock {s : ℕ} (hs : 1≤s) :
    (∀ (n m t : ℕ),WernerAsymptotics.coefficient n m s t=Occupation.wernerWeight n m (s+1) t) ∧
    (∀ (L : ℕ) (S : Finset (Fin L)),
      (GeneralSymmetricOccupation.occupationRecovery L s).toLinearMap
        (GeneralSymmetricOccupation.wernerOutput (s:=s) S)=
      InfiniteOccupationStates.occupationOperator (@GeneralSymmetricOccupation.numberVector s) S.card L) ∧
    (∀ (m : ℕ→ℕ) (hm : ∀ n,n≤m n) (γ : ℝ),1<γ →
      Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ) →
      Tendsto (fun n => ‖(GeneralSymmetricOccupation.occupationRecovery (m n) s).toLinearMap
        (GeneralSymmetricOccupation.wernerOutput (s:=s) (GeneralSymmetricOccupation.inputSlots n (m n) (hm n)))-
        InfiniteOccupationStates.thermalOperator (@GeneralSymmetricOccupation.numberVector s) γ‖)
        atTop (𝓝 0)) := by
  sorry

/-- prop:grassmann-pct-comparison. Rank is r+1 and ambient dimension r+1+k. The internal purifier has dimension (r+1)^2; r*(r+2) is its dimension minus one. -/
theorem grassmann_pct_factorization (r k : ℕ) (P : PhysicalFlatGrassmann.Projector (r+1) k) (n t : ℕ) :
    PhysicalFlatPCT.fidelity r k P n t=
      Real.sqrt (PCTRankAdapted.supportFactor n (n+t) (r*(r+2))
        (PCTRankAdapted.flatPurificationDimension r k))*
      (PCTPhysicalState.outputState (PCTRankAdapted.flat_internal_register_card r)
        (PCTRankAdapted.flatInternalState r) n t).rootFidelity
          (tensorState (PCTRankAdapted.flatInternalState r) (n+t)) := by
  sorry

/-- prop:pct-projector-small-error. The fixed-gain fidelity limit is not assumed. Error is 1-F², with fixed δ then large n then δ→0; rank is r+1. -/
theorem pct_projector_small_error (r k : ℕ) :
    (∀ (P : PhysicalFlatGrassmann.Projector (r+1) k) (m : ℕ→ℕ) (δ : ℝ),
      0<δ → δ<1/(2*((r+1:ℕ):ℝ)) →
      Tendsto (fun n => (m n:ℝ)/(n:ℝ)) atTop (𝓝 (1+δ)) →
      PCTProjectorPurity.lowerEnvelope ((r+1)*k) δ≤
        liminf (fun n => 1-PCTPrescribed.rankFidelity r k P n (m n)^2) atTop ∧
      liminf (fun n => 1-PCTPrescribed.rankFidelity r k P n (m n)^2) atTop≤
        limsup (fun n => 1-PCTPrescribed.rankFidelity r k P n (m n)^2) atTop ∧
      limsup (fun n => 1-PCTPrescribed.rankFidelity r k P n (m n)^2) atTop≤
        PCTProjectorPurity.upperEnvelope ((r+1)*k) (r*(r+2)) δ) ∧
    (∀ t : ℝ→ℕ→ℕ,
      (∀ δ,0<δ → δ<1/(2*((r+1:ℕ):ℝ)) →
        Tendsto (fun n => ((n+t δ n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1+δ))) →
      ∀ η>0,∀ᶠ δ in 𝓝[>] (0:ℝ),∀ᶠ n : ℕ in atTop,
        ∀ P : PhysicalFlatGrassmann.Projector (r+1) k,
          |(1-PhysicalFlatPCT.fidelity r k P n (t δ n)^2)/δ-(((r+1)*k:ℕ):ℝ)|≤η) := by
  sorry

end CloningVerification
