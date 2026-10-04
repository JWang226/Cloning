import Cloning.PCTPrescribedRankGuarantee
import Cloning.PCTProjectorPurityTargets
import Cloning.PCTHybridMixtureChannel
import Cloning.PCTTangentChartAdmissible
import Cloning.MultimodeCoherentGaussianMixture
import Cloning.InfiniteDiagonalFidelity
import Cloning.PCTGaussianAssembly
import Cloning.PCTPurificationChannelPhysical
import Cloning.ThermalParameterContinuity
import Cloning.PCTGlobalPhysical
import Cloning.PCTGaussianCovarianceJoint
import Cloning.PCTGaussianOutput
import Cloning.PCTGaussianOutputTangent
import Cloning.PCTTangentNormalization
import Cloning.PCTPhysicalStateSpectrum
import Cloning.PhysicalCloningPCTTheorem
import Cloning.PhysicalFlatPCTTheorem
import Cloning.PhysicalFlatPCTFinite
import Cloning.SampleRatioLimit

/-!
# Coherent thermal identities and physical PCT product mixtures

Finite product circular Gaussian mixtures of coherent projectors equal actual
thermal operators as trace-class Bochner integrals. Thermal operators are continuous
in their parameters down to vacuum, and the physical amplifier has the exact thermal
output throughout [0,1). The actual full-environment Haar purification channel is
part of an actual state-independent global CPTP cloning channel, with an exact
physical formula and Gaussian mixture limit. The joint classical/orbital tangent
characteristic is calculated from the actual purification-frame Gaussian, and an
actual random-displacement channel has the PCT thermal output. The complete joint
tangent law is proved, with independence derived by characteristic uniqueness. Its
actual hybrid translation average equals the broadened Gaussian–thermal state and
has root fidelity pctValue. The exact local exponential chart has an inverse with
the required scaled tangent-coordinate limit. For an arbitrary positive definite
density with distinct eigenvalues, spectral diagonalization and all physical PCT
adapters and the compact-window mixed-LAN construction are proved. Its physical
full-environment fidelity limit is unconditional. The smaller-environment
projector PCT comparison is tracked separately in `PROGRESS.md`.

This entry point adds no definitions or proofs.
-/

#check Cloning.MultimodeCoherentGaussianMixture.integral_coherentProjector_gaussian_eq_productThermal
#check Cloning.InfiniteDiagonalFidelity.stateFidelity_productGeometric
#check Cloning.PCT.exists_pct_product_mixture
#check Cloning.PCT.randomizedPurificationOutput_eq
#check Cloning.PCT.wernerOutput_physical_purification
#check Cloning.MultimodeCoherent.productThermal_tendsto
#check Cloning.MultimodeAmplifier.gainChannel_productThermal_nonneg
#check Cloning.PCTPurificationChannel.partialTrace_purification_tensor
#check Cloning.PCTPurificationChannel.physicalPurification_eq_environmentRotate
#check Cloning.PCTPurificationChannel.physical_pct_gaussian_product_mixture
#check Cloning.PCTGlobal.channel_gaussian_product_mixture
#check Cloning.PCTGaussianCovariance.jointCoordinate_characteristic
#check Cloning.PCTGaussianOutput.tangent_displacement_productThermal_pct
#check Cloning.PCTReducedGaussian.normalizedTangentVector_norm
#check Cloning.PCTReducedGaussian.normalizedTangent_remainder

#check Cloning.PCTJointGaussianLaw.jointTangent_map_eq_prod
#check Cloning.PCTJointGaussianWhitening.whitenedJointTangent_map_eq_prod
#check Cloning.PCTHybridMixture.tangent_hybrid_average_eq_pctGaussianThermalPositive
#check Cloning.PCTHybridMixture.tangentMixtureChannel
#check Cloning.PCTHybridMixture.tangentMixtureChannel_fidelity_eq_pctValue
#check Cloning.PCTHybridMixture.exists_tangentMixtureChannel_fidelity
#check Cloning.PCTLocalChart.chart_hasStrictFDerivAt_zero
#check Cloning.PCTLocalChart.eventually_tangent_exact_chart
#check Cloning.PCTLocalChart.scaledSpectralCoordinates_tendsto
#check Cloning.PCTLocalChart.scaledOrbitalCoordinates_tendsto

#check Cloning.PCTLocalChart.eventually_frameParticle_exact_chart
#check Cloning.PCTLocalChart.frameParticle_spectral_parameters
#check Cloning.PCTLocalChart.frameParticle_orbital_parameters

#check Cloning.PCTLocalChart.eventually_sample_chart_admissible
#check Cloning.PCTLocalChart.exists_compact_ball_sampleParameters
#check Cloning.PCTPhysicalState.physical_pct_fidelity_of_simple_density
#check Cloning.PCTPhysicalState.physical_pct_fidelity

#check Cloning.PhysicalFlatPCT.fidelity_eq_supportFactor
#check Cloning.PhysicalFlatPCT.fidelity_limsup_le

#check Cloning.PCTRankAdapted.outputState_fidelity_lower
#check Cloning.PhysicalFlatPCT.prescribed_fidelity_sq_ge_target
#check Cloning.SampleRatio.threshold_expansion
#check Cloning.SampleRatio.threshold_relative_tendsto

#check Cloning.PCTProjectorPurity.frameMixture_scaled_purity_tendsto
#check Cloning.PCTProjectorPurity.prescribed_error_liminf_limsup
#check Cloning.PCTProjectorPurity.physical_small_gain_coefficient
#check Cloning.PCTProjectorPurity.physical_target_brackets

#check Cloning.PCTPrescribed.rankChannel_statePayoff_lower
#check Cloning.PCTPrescribed.rankChannel_uniform_sample_guarantee
#check Cloning.PCTPrescribed.rankChannel_uniform_asymptotic_lower
#check Cloning.PCTPrescribed.rankChannel_liminf_lower
