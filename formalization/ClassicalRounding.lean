import Cloning.YoungPhysicalRoundingUniformDensity
import Cloning.TensorSchurDecompositionSharpConcentration
import Cloning.YoungRounding
import Cloning.GaussianAffinity
import Cloning.YoungTwoRowAsymptotics
import Cloning.YoungTwoRowConcentration
import Cloning.YoungCompatibilityFallback
import Cloning.YoungHyperplaneSampling
import Cloning.YoungHyperplaneCovariance
import Cloning.YoungGeneralFallback
import Cloning.YoungGeneralMoments
import Cloning.YoungNormalizationLimits
import Cloning.YoungHookRatioLimit
import Cloning.YoungUniformLocalMultinomial
import Cloning.YoungUniformLocalPhysicalL1
import Cloning.YoungUniformLocalQuantization
import Cloning.TensorSchurDecompositionConcentration
import Cloning.YoungPhysicalRounding
import Cloning.YoungFlatLimit
import Cloning.YoungFlatCouplingRank

/-!
# Classical rounding, Young concentration, and dimension moments

The literal general-rank tableau weights have proved normalization through finite
RSK/Pieri and define an actual Young-label PMF. Uniform exponential concentration
includes repeated and zero spectral coordinates. The constructed law has vanishing
compatibility-fallback error under the stated interior-spectrum hypotheses and
forward/inverse crossing-root dimension moments at the flat spectrum.
Root-hyperplane geometry and rank-two rates are retained. The literal standard-word
count has the exact factorial determinant, Vandermonde and pair-ratio formulas.
The multinomial local limit is uniform over moving positive spectra and bounded
central windows. The actual physical Schur probability law is now identified. Its smoothed
Young local limit and reverse quantization errors converge in L1 uniformly
over compact subsets of the strictly ordered positive simplex.
The actual flat law has a normalized Vandermonde-Gaussian full L1 limit.
Exact finite couplings of the physical flat laws have vanishing incompatibility
and the required averaged sector-fidelity limit.

This entry point adds no definitions or proofs.
-/

#check Cloning.YoungRounding.roundedDensity_l1_of_local_limit
#check Cloning.YoungCompatibility.eventually_fallback_error_bounds
#check Cloning.YoungCompatibility.fallback_errors_tendsto_zero
#check Cloning.YoungHyperplane.volume_eq_sqrt_smul_coordinateMeasure
#check Cloning.YoungHyperplane.sampleInterpolate_l1_isometry
#check Cloning.YoungHyperplane.rootCovariance_det
#check Cloning.YoungHyperplane.rootCovarianceEquiv_inverse_quadratic
#check Cloning.YoungTwoRow.meanDimensionRatio_relative_isBigO
#check Cloning.YoungTwoRow.meanInverseDimensionRatio_relative_isBigO
#check Cloning.YoungGeneral.atypicalMass_le
#check Cloning.YoungGeneral.tableau_fallback_errors_tendsto_zero
#check Cloning.YoungGeneral.dimension_moments_tendsto_one
#check Cloning.YoungGeneral.totalTableauMass_eq_pow
#check Cloning.YoungGeneral.tableauPMF
#check Cloning.YoungGeneral.tableauPMF_tailProbability_tendsto_zero
#check Cloning.YoungGeneral.tableauPMF_fallback_errors
#check Cloning.YoungGeneral.flatTableauPMF_dimension_moments
#check Cloning.YoungGeneral.standardCount_eq_factorial_determinant
#check Cloning.YoungGeneral.standardCount_eq_vandermonde
#check Cloning.YoungGeneral.standardCount_eq_multinomial_correction
#check Cloning.YoungGeneral.tableauCorrection_tendsto
#check Cloning.YoungMultinomial.uniform_multinomial_local_limit

#check Cloning.YoungHyperplane.uniform_tensorYoungDensity_l1
#check Cloning.YoungHyperplane.uniform_quantized_covarianceGaussian_l1
#check Cloning.TensorLie.tensorYoungPMF_tail_tendsto_zero
#check Cloning.YoungHyperplane.uniform_tensorYoungFallbackOutput_affinity
#check Cloning.YoungFlat.flatDensity_l1_tendsto
#check Cloning.YoungFlatCoupling.rankFlatCoupling_map_fst
#check Cloning.YoungFlatCoupling.rankFlatCoupling_map_snd
#check Cloning.YoungFlatCoupling.rankFlatCoupling_fidelity_tendsto

#check Cloning.TensorLie.exists_tensorYoungPMF_uniform_exp_threshold

#check Cloning.YoungHyperplane.uniform_rounded_tensorYoungDensity_l1
