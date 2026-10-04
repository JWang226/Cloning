import Cloning.HybridWeightedFidelityLimit
import Cloning.InfiniteChannelFidelity
import Cloning.InfiniteFidelityContinuity
import Cloning.InfiniteFidelityRegularized
import Cloning.InfiniteFidelityConcavity
import Cloning.HybridWeightedFidelity
import Cloning.HybridJensenSigmaFinite
import Cloning.HybridThermalWitness
import Cloning.HybridWeightedTrace
import Cloning.HybridGaussianMass
import Cloning.HybridL1Jensen
import Cloning.HybridGaussianAttainmentBoundary
import Cloning.MixedChannelsFidelity
import Cloning.MixedChannelsPreparation
import Cloning.MixedChannelsBounded
import Cloning.MixedChannelsReverseFidelity

/-!
# Quantum and continuous classical-quantum fidelity

Actual positive trace-class operators and integrable operator fields satisfy
continuity, data processing, weighted fidelity bounds, and sigma-finite Bochner
Jensen. Concrete Gaussian/thermal witnesses have proved inverse moments and
integrability. Fidelity and Bochner Jensen also hold directly on the positive L1
space used by actual classical-quantum channels. Preparation, a completely positive
L1 map, and weighted integration compose to a completely positive quantum map.
Actual quantum-to-hybrid and hybrid-to-quantum channel interfaces carry all-input
finite-ancilla CP and trace preservation, with genuine preparation/integration
examples, boundedness, and fidelity data processing in both directions. Reverse
data processing follows by positive simple-field approximation and finite block
witnesses, without a measurable-optimizer assumption.
The sharp residual trace estimate and Gaussian classical-quantum optimum are proved,
with physical attainment and all thermal parameters in [0,1). Transferring this
Gaussian result to physical mixed-state cloning still requires mixed-state LAN.

This entry point adds no definitions or proofs.
-/

#check Cloning.InfiniteFidelity.fidelity_data_processing
#check Cloning.InfiniteFidelity.stateFidelity_continuity
#check Cloning.InfiniteFidelity.fidelity_weighted_joint_concavity
#check Cloning.Hybrid.PositiveField.rootFidelity_continuity
#check Cloning.Hybrid.PositiveField.integral_fidelity_le_fidelity_integral
#check Cloning.Hybrid.PositiveField.rootFidelity_sq_le_weighted_product
#check Cloning.Hybrid.PositiveField.rootFidelity_sq_le_gaussian_thermal
#check Cloning.Hybrid.weightedQuantumMap_completelyPositive
#check Cloning.Hybrid.weightedQuantumMap_trace_le
#check Cloning.Hybrid.gaussian_shift_weighted_mass_le
#check Cloning.Hybrid.PositiveField.toL1_ofL1
#check Cloning.Hybrid.PositiveL1.continuous_rootFidelity
#check Cloning.Hybrid.PositiveL1.integral_rootFidelity_le
#check Cloning.Hybrid.weightedQuantumMap_gaussian_trace_le
#check Cloning.Hybrid.exists_gaussian_weighted_covariant_residual
#check Cloning.Hybrid.gaussianAmplifierChannel_orbitPayoff
#check Cloning.Hybrid.PhaseDensity.gaussianOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.Hybrid.QuantumToHybrid.fidelity_data_processing
#check Cloning.Hybrid.QuantumToHybrid.prepare
#check Cloning.Hybrid.HybridToQuantum.integrate
#check Cloning.Hybrid.HybridToQuantum.norm_le_two
#check Cloning.Hybrid.HybridToQuantum.fidelity_data_processing

#check Cloning.InfiniteFidelity.fidelity_sq_le_of_regularized_inverse_limit
#check Cloning.Hybrid.PositiveField.rootFidelity_sq_le_weighted_productPositive_of_inverse_limit
