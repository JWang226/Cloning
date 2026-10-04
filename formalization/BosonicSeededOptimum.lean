import Cloning.ScoreReferenceMeasure
import Cloning.HybridGaussianScoreOptimum
import Cloning.OrbitalSeededOptimum
import Cloning.MultimodeLeastNoise
import Cloning.BosonicAmplifierThermal
import Cloning.WeylCovariantMultiplier
import Cloning.WeylMultimodeChannel
import Cloning.UniversalGaussianRealBox
import Cloning.WeylIdlerUniqueness
import Cloning.OrbitalGaussianAttainmentBoundary
import Cloning.WeylQuantumBochner
import Cloning.WeylDiagonalRepresentation
import Cloning.WeylSqueezerUnitary
import Cloning.WeylSqueezerRepresentation
import Cloning.CovariantAmplifierLeastNoise

/-!
# Universal orbital Gaussian optimum and physical attainment

The optimized average root fidelity over expanding real boxes converges to the
product of thermal mode factors. The supremum ranges over all actual CPTP channels
at each radius, including channels coupling the modes. The physical quantum-limited
amplifier attains this value at every radius. Thermal parameters lie in [0,1),
including vacuum modes, and the gain is greater than one.

Normal Heisenberg duals, quantum-positive multipliers, and the sharp thermal witness
moment are derived from the channel. The proof needs no idler reconstruction.
Continuous quantum-positive characteristic reconstruction now constructs a
unique actual joint trace-class idler. This applies to arbitrary mode-dependent
amplifier gains, without a product or Gaussian restriction on the idler. The
full doubled-Fock squeezing unitary and its arbitrary-input reduced dilation are
constructed. Exact identification with the seeded number law proves the sharp
bound for all nonnegative antitone product observables and actual covariant CP/TNI
maps, retaining the exact output trace even at zero success probability.

This entry point adds no definitions or proofs.
-/

#check Cloning.OrbitalSeededOptimum.isGreatest_payoff
#check Cloning.MultimodeLeastNoise.productObservable_moment_le
#check Cloning.BosonicAmplifier.stateFidelity_channel_gain
#check Cloning.MultimodeCoherent.displacement_commutant_scalar
#check Cloning.MultimodeCoherent.eigenoperator_eq_scalar_displacement
#check Cloning.MultimodeCoherent.covariant_linearMap_weyl_multiplier
#check Cloning.MultimodeCoherent.quantumChannel_regular_quantumPositive_multiplier
#check Cloning.MultimodeCoherent.quantumChannel_weyl_gaussian_bound
#check Cloning.MultimodeCoherent.covariant_thermal_witness_moment_le
#check Cloning.MultimodeCoherent.limsup_flatBox_thermal_le_modeFactor

#check Cloning.MultimodeCoherent.limsup_realFlatBox_thermal_le_modeFactor
#check Cloning.MultimodeAmplifier.gainChannel_covariant
#check Cloning.MultimodeAmplifier.gainChannel_productThermal_nonneg
#check Cloning.MultimodeCoherent.gainChannel_orbitPayoff_nonneg
#check Cloning.MultimodeCoherent.gainChannel_normalized_box_nonneg
#check Cloning.MultimodeCoherent.limsup_realFlatBox_thermal_le_modeFactor_nonneg
#check Cloning.MultimodeCoherent.realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg

#check Cloning.WeylGNS.existsUnique_density_characteristic
#check Cloning.WeylGNS.covariantChannel_existsUnique_idler
#check Cloning.MultimodeCoherent.quantumChannel_diagonal_existsUnique_idler
#check Cloning.MultimodeCoherent.quantumChannel_diagonal_idler_representation
#check Cloning.WeylSqueezer.squeeze_signal_heisenberg
#check Cloning.WeylSqueezer.covariantChannel_exists_dilation
#check Cloning.CovariantAmplifier.thermalOutput_exists_seeded_idler
#check Cloning.CovariantAmplifier.covariant_cpTNI_product_moment_le

#check Cloning.Hybrid.PhaseBody.gaussian_optimalPayoff_tendsto
#check Cloning.PCTJointGaussianWhitening.scoreGaussianOptimal_tendsto

#check Cloning.PCTJointGaussianWhitening.scoreReferenceMeasure_eq_intrinsic
#check Cloning.PCTJointGaussianWhitening.normalized_score_integral_eq_intrinsic
