import Cloning.HybridGaussianScoreOptimum
import Cloning.InfiniteAsymptoticCPCompactness
import Cloning.InfiniteCutoffChannels
import Cloning.ChannelAveraging
import Cloning.WeylFoelnerLimit
import Cloning.WeylFlatPriorThermal
import Cloning.HeisenbergDualResidual
import Cloning.UniversalGaussianRealBox
import Cloning.HybridGaussianBoundary
import Cloning.UniversalGaussianBoundary

/-!
# Common-subsequence CP limits and flat-prior payoff transfer

Actual CPTP averages over expanding flat boxes have uniform vanishing covariance
defect. A common CP trace-nonincreasing limit preserves the required compact-witness
payoff estimate for scale-dependent competitors. Covariance forces any nonzero
limit to be a scalar multiple of a genuine CPTP channel. Actual L1 hybrid channels
also admit completely positive trace-preserving averages. Their weighted quantum
residual has the sharp classical Gaussian trace bound, derived from classical
translation covariance. These results give the orbital and hybrid Gaussian
converses, with the supremum over channels before the prior limit, including real
box radii and thermal parameters in [0,1). Escaping trace is allowed in the limits.

This entry point adds no definitions or proofs.
-/

#check Cloning.InfiniteTraceClass.exists_subsequence_covariant_cp_limit_of_limsup_trace_bound
#check Cloning.InfiniteTraceClass.QuantumChannel.finiteBasisCutoff_tendstoUniformlyOn
#check Cloning.InfiniteTraceClass.QuantumChannel.average
#check Cloning.MultimodeCoherent.gaussianFoelnerChannel_covariance_tendsto_all
#check Cloning.MultimodeCoherent.exists_gaussianFoelner_covariant_limit
#check Cloning.MultimodeCoherent.exists_flatBox_thermal_payoff_limit
#check Cloning.MultimodeCoherent.covariant_cpTNI_zero_or_scaled_channel
#check Cloning.MultimodeCoherent.limsup_flatBox_thermal_le_modeFactor

#check Cloning.MultimodeCoherent.limsup_realFlatBox_thermal_le_modeFactor
#check Cloning.Hybrid.L1BlockPositive_integral
#check Cloning.Hybrid.Channel.average
#check Cloning.Hybrid.PhaseDensity.foelnerMap_covariance_tendsto_varying
#check Cloning.Hybrid.exists_gaussian_weighted_covariant_residual
#check Cloning.Hybrid.eventually_gaussianThermal_output_rootFidelity_le
#check Cloning.MultimodeCoherent.limsup_realFlatBox_thermal_le_modeFactor_nonneg
#check Cloning.Hybrid.limsup_realFlatBox_gaussian_le_modeFactor_nonneg

#check Cloning.PCTJointGaussianWhitening.scoreGaussianOptimal_limsup_le
