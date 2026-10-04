import Cloning.PCTJointGaussianChart
import Cloning.PCTMixedMixtureTransfer
import Cloning.HybridCoordinateTransport
import Cloning.InfiniteLANTransfer
import Cloning.GeneralCoherentChannels
import Cloning.HybridJensenSigmaFinite
import Cloning.UniversalGaussianRealBox
import Cloning.OrbitalGaussianAttainmentBoundary
import Cloning.HybridGaussianAttainmentBoundary
import Cloning.MixedLANTransfer
import Cloning.MixedGaussianConverse
import Cloning.MixedChannelsFiniteSelector
import Cloning.PCTPhysicalFidelityLAN
import Cloning.TensorLANEmbeddingCompactLAN

/-!
# Quantum-channel LAN and statistical transfer

Channel-composition fidelity estimates and minimax-to-Bayes reduction use actual
channels, including quantum-to-hybrid and hybrid-to-quantum CPTP maps. The mixed
converse transfer has a competitor-independent square-root error bound and allows
approximation hypotheses almost everywhere under the chosen prior. Pure product
models have compact-uniform two-way coherent comparison maps. Pointwise mixed
approximations pass through actual Bochner mixtures by scalar dominated convergence,
including varying physical registers and unbounded Gaussian support. The final
two-sided fidelity squeeze is proved from explicit approximation hypotheses. Actual
measure-preserving coordinate equivalences transport all hybrid CPTP competitors
and preserve their payoff.
Finite Kraus instruments with classical outcome densities and finite measurable
selectors construct genuine channels in both directions on all inputs.
Both the orbital and full classical-quantum Gaussian optima are proved over all
actual CPTP competitors, with physical amplifier/dilation attainment. The channel
supremum precedes the expanding-prior or real-box limit; vacuum thermal modes are
included. Actual mixed-state forward/reverse LAN channels are now constructed;
one sequence works on every compact parameter window. The physical Schur,
Young, Gibbs and local-unitary approximations are discharged internally.

This entry point adds no definitions or proofs.
-/

#check Cloning.InfiniteLANTransfer.fidelity_transfer
#check Cloning.InfiniteLANTransfer.minimax_le_bayesValue
#check Cloning.GeneralCoherent.exists_twoWay_coherent_product_channels
#check Cloning.Hybrid.PositiveField.integral_fidelity_le_fidelity_integral
#check Cloning.MultimodeCoherent.limsup_flatBox_thermal_le_modeFactor

#check Cloning.MultimodeCoherent.limsup_realFlatBox_thermal_le_modeFactor
#check Cloning.Hybrid.PositiveL1.integral_rootFidelity_le
#check Cloning.MultimodeCoherent.realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.Hybrid.PhaseDensity.gaussianOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.Hybrid.realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.MixedLANTransfer.fidelity_transfer
#check Cloning.MixedLANTransfer.minimax_le_bayesValue_ae
#check Cloning.MixedLANTransfer.limsup_minimax_le_modeFactor_of_mixed_approximation

#check Cloning.MixedLANTransfer.fidelity_sandwich_of_twoWay_mixed
#check Cloning.MixedLANTransfer.fidelity_tendsto_of_twoWay_mixed_approximation
#check Cloning.MixedLANTransfer.forward_mixture_tendsto
#check Cloning.MixedLANTransfer.reverse_mixture_tendsto
#check Cloning.MixedLANTransfer.fidelity_tendsto_of_mixed_mixture
#check Cloning.Hybrid.QuantumToHybrid.finiteKrausInstrument
#check Cloning.Hybrid.HybridToQuantum.finiteSelector
#check Cloning.PCTPhysicalFidelity.CompactWindowLAN.moving_parameters
#check Cloning.Hybrid.Channel.coordinateEquiv
#check Cloning.Hybrid.Channel.transportCoordinates_rootFidelity

#check Cloning.PCTJointGaussianWhitening.whiteningEquiv
#check Cloning.PCTJointGaussianWhitening.whitening_measurePreserving
#check Cloning.PCTJointGaussianWhitening.scoreChannelEquiv
#check Cloning.PCTJointGaussianWhitening.classicalTangentLaw_eq_unwhiten_map
#check Cloning.TensorLAN.physicalCompactWindowLAN
