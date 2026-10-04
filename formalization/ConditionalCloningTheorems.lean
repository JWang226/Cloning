import Cloning.QubitDegeneracy
import Cloning.CloningValueComparisonInfimum
import Cloning.CloningValueComparisonLargeGain
import Cloning.SpectralRatioMajorizationCounterexample
import Cloning.PhysicalAllStateMinimaxBounds
import Cloning.SpectralGapThreshold
import Cloning.PhysicalCloningSmallError
import Cloning.CloningValueBoundaryCoefficients
import Cloning.ThermalNearPure
import Cloning.CloningValueExpansionTarget
import Cloning.Main
import Cloning.PCTGaussianAssembly
import Cloning.UniversalGaussianRealBox
import Cloning.OrbitalGaussianAttainmentBoundary
import Cloning.HybridGaussianAttainmentBoundary
import Cloning.PCTPurificationChannelPhysical
import Cloning.PCTGlobalPhysical
import Cloning.PCTGaussianCovarianceJoint
import Cloning.PCTPhysicalStateSpectrum
import Cloning.PhysicalCloningKnownTheorem
import Cloning.PhysicalCloningUniversalTheorem
import Cloning.PhysicalCloningPCTTheorem
import Cloning.TensorCloningUniformKnown
import Cloning.TensorCloningUniformUniversal
import Cloning.PhysicalFlatGrassmannTheorem
import Cloning.PhysicalFlatPCTTheorem
import Cloning.PCTClosedForm
import Cloning.PCTPrescribedFull
import Cloning.PCTPrescribedRankTheorem
import Cloning.TensorCloningPrescribedLimits
import Cloning.SpectralAffineTheorem

/-!
# Physical cloning limits and the earlier conditional assembly

Known- and unknown-spectrum minimax convergence is proved for the actual
optimization over all physical CPTP maps. The unknown-spectrum theorem requires
a compact nonempty spectral set equal to the closure of its interior. The earlier
conditional assembly remains available with its original explicit hypotheses.
The orbital and hybrid Gaussian optimization
problems are solved over actual channels, with physical attainment and vacuum
thermal modes included. The full-environment Haar purification channel and its
actual state-independent global PCT channel, exact physical formula, and Gaussian
reduced-product mixture are proved.

The strict comparison of scalar limiting formulas is proved. Actual Schur
decomposition, sector-state limits, the physical Young law, and compact-window
two-way LAN are constructed. The physical full-environment PCT fidelity limit
is unconditional at arbitrary positive simple density matrices in dimension
at least two. Both prescribed cloners have exact compact-uniform two-sided
fidelity limits and all-input covariance. The flat Grassmann minimax is proved
for every literal rank-r orthogonal projector. The actual fixed rank-adapted PCT channel satisfies the projector upper bound
and strict gap for rank greater than one. Remaining standalone manuscript scope
and fresh verification are tracked in `PROGRESS.md`.

This entry point adds no definitions or proofs.
-/

#check Cloning.known_spectrum_optimum_of_bounds
#check Cloning.unknown_spectrum_optimum_of_bounds
#check Cloning.pctValue_lt_universalValue
#check Cloning.PCT.exists_pct_product_mixture
#check Cloning.MultimodeCoherent.limsup_flatBox_thermal_le_modeFactor

#check Cloning.MultimodeCoherent.limsup_realFlatBox_thermal_le_modeFactor
#check Cloning.MultimodeCoherent.realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.Hybrid.PhaseDensity.gaussianOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.Hybrid.realFlatBoxOptimalPayoff_tendsto_modeFactor_nonneg
#check Cloning.PCTPurificationChannel.haarPurificationChannel_tensorPower
#check Cloning.PCTPurificationChannel.physical_pct_gaussian_product_mixture
#check Cloning.PCTGlobal.channel_matrix_apply
#check Cloning.PCTGlobal.channel_gaussian_product_mixture
#check Cloning.PCTGaussianCovariance.jointCoordinate_characteristic
#check Cloning.PCTPhysicalState.physical_pct_fidelity_of_simple_density
#check Cloning.TensorCloning.knownSpectrumValue_tendsto
#check Cloning.TensorCloning.unknownSpectrumValue_tendsto
#check Cloning.TensorCloning.unknownSpectrumValue_tendsto_affine
#check Cloning.PCTPhysicalState.physical_pct_fidelity

#check Cloning.TensorCloning.eventually_uniform_knownSpectrumChannel_payoff
#check Cloning.TensorCloning.eventually_uniform_universalChannel_payoff
#check Cloning.PhysicalFlatGrassmann.minimaxValue_tendsto

#check Cloning.PhysicalFlatPCT.fidelity_limsup_le
#check Cloning.PhysicalFlatPCT.fidelity_limsup_lt_optimal
#check Cloning.PhysicalFlatPCT.fidelity_uniform_upper
#check Cloning.pctValue_closedForm
#check Cloning.PCTPrescribed.fullChannel_fidelity_tendsto
#check Cloning.PCTPrescribed.rankFidelity_limsup_lt_optimal
#check Cloning.PCTPrescribed.rankFidelity_uniform_upper

#check Cloning.ValueExpansion.orbital_squared_remainder
#check Cloning.ValueExpansion.universal_squared_remainder
#check Cloning.ValueExpansion.pct_squared_remainder
#check Cloning.ValueExpansion.universalCoefficient_lt_pctCoefficient
#check Cloning.ValueExpansion.universal_target_brackets
#check Cloning.ValueExpansion.pct_target_brackets

#check Cloning.ValueComparison.universalValue_iInf
#check Cloning.ValueComparison.majorization_does_not_order_universal
#check Cloning.ValueComparison.allStateUpperBound_largeGain_tendsto
#check Cloning.PhysicalAllStateMinimax.all_density_minimax_bounds
#check Cloning.SpectralGap.gapSet_minimax_tendsto
#check Cloning.SpectralGap.gapSet_threshold_not_regular
#check Cloning.ValueExpansion.known_physical_target_brackets
#check Cloning.ValueExpansion.pct_physical_target_brackets
#check Cloning.ValueExpansion.knownCoefficient_tendsto_atTop_of_smallest

#check Cloning.QubitDegeneracy.concrete_noncommuting_limits
#check Cloning.ValueExpansion.universal_physical_target_brackets
