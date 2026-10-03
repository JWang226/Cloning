import Cloning.InfiniteAsymptoticCPCompactness
import Cloning.InfiniteCutoffChannels
import Cloning.ChannelAveraging
import Cloning.WeylFoelnerLimit

/-!
# Common-subsequence CP limits and concrete covariant averages

Uniformly bounded CP maps on separable Hilbert spaces admit one common subsequence
converging on every input and compact observable, with the stated limsup trace bound.
Actual CPTP Bochner averages and explicit expanding Gaussian priors now supply
trace-norm approximate covariance for every trace-class input and construct an
exactly covariant common-subsequence CP limit. Trace loss in that limit is allowed. Payoff preservation and the manuscript-specific weighted trace
bound are separate from this Gaussian averaging construction.

This entry point adds no definitions or proofs.
-/

#check Cloning.InfiniteTraceClass.exists_subsequence_covariant_cp_limit_of_limsup_trace_bound
#check Cloning.InfiniteTraceClass.QuantumChannel.finiteBasisCutoff_tendstoUniformlyOn
#check Cloning.InfiniteTraceClass.QuantumChannel.average
#check Cloning.MultimodeCoherent.gaussianFoelnerChannel_covariance_tendsto_all

#check Cloning.MultimodeCoherent.exists_gaussianFoelner_covariant_limit
