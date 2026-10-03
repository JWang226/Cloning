import Cloning.YoungRounding
import Cloning.GaussianAffinity
import Cloning.YoungTwoRowAsymptotics
import Cloning.YoungTwoRowConcentration
import Cloning.YoungCompatibilityFallback
import Cloning.YoungHyperplaneSampling
import Cloning.YoungHyperplaneCovariance

/-!
# Classical rounding, compatibility, and root-hyperplane geometry

Coordinate rounding, the actual Young-label fallback PMF, and its error controlled by
atypical mass are proved. The sum-zero Euclidean hyperplane is identified with the
coordinate lattice, with exact cell volumes, fidelity/L1 identities, and covariance
determinant and inverse formulas. Both concrete two-row dimension moments are proved.
General-rank Young-law concentration and uniform local limits remain separate inputs.

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
