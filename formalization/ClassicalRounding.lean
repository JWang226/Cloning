import Cloning.YoungRounding
import Cloning.GaussianAffinity
import Cloning.YoungTwoRowAsymptotics
import Cloning.YoungTwoRowConcentration

/-!
# Classical rounding and concrete Young-law moments

The coordinate-lattice rounding PMF, exact dilation/averaging bridge, fixed-reference
density convergence from local estimates, Gaussian affinity integral, and both concrete
two-row dimension moments are proved. Root-hyperplane measure identification, Young
compatibility fallback, its negligible mass, the general-rank local limit, and compact-
spectrum uniformity are not proved.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.YoungRounding.roundedDensity_l1_of_local_limit
#check Cloning.YoungRounding.rounding_intertwining_scaled
#check Cloning.GaussianAffinity.integral_product_dilation_eq_classicalValue
#check Cloning.YoungTwoRow.meanDimensionRatio_relative_isBigO
#check Cloning.YoungTwoRow.meanInverseDimensionRatio_relative_isBigO
