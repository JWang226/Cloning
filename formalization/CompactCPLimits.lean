import Cloning.InfiniteAsymptoticCPCompactness
import Cloning.InfiniteCutoffChannels

/-!
# Common-subsequence compact CP limits

On separable Hilbert spaces, actual uniformly bounded CP maps with the stated limsup
trace bound admit one common subsequence converging on every input and compact
observable. Approximate covariance passes to that same limit; trace loss is allowed.
Actual finite-output cutoff channels converge uniformly on compact positive input sets.
Construction and estimates of the manuscript-specific averaged maps remain separate.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.InfiniteTraceClass.exists_subsequence_covariant_cp_limit_of_limsup_trace_bound
#check Cloning.InfiniteTraceClass.QuantumChannel.finiteBasisCutoff_tendstoUniformlyOn
