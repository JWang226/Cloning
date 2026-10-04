import Cloning.TensorPositiveSpectrumCompressionFidelity
import Cloning.MatrixFidelityProjector
import Cloning.YoungDimensionRatio
import Cloning.YoungDimensionSecondOrder
import Cloning.YoungGeneralMoments
import Cloning.YoungNormalizationLimits
import Cloning.PhysicalFlatGrassmannTheorem
import Cloning.PhysicalFlatGrassmannUniform
import Cloning.PhysicalFlatCloningTheorem
import Cloning.TensorFlatProjectorAchievability
import Cloning.YoungDimensionMomentRateAsymptotics
import Cloning.PhysicalFlatRateBounded
import Cloning.TensorRankOneGlobal

/-!
# Projector converse and dimension factors

The exact flat-projector minimax limit is proved over all genuine physical
channels and all literal Hermitian idempotent rank-r projectors. Spectral orbit
exhaustion, the actual flat Schur law, dimension moments, finite converse and
an explicit globally achievable channel are constructed. The value is
γ^(-r*k/2) in ambient dimension r+k, including k=0.

This entry point adds no definitions or proofs.
-/

#check Cloning.MatrixFidelity.finite_kraus_projector_converse
#check Cloning.YoungDimensionRatio.projector_sector_factor_tendsto
#check Cloning.YoungGeneral.dimension_moments_tendsto_one
#check Cloning.YoungGeneral.totalTableauMass_eq_one
#check Cloning.YoungGeneral.flatTableauPMF
#check Cloning.YoungGeneral.flatTableauPMF_dimension_moments

#check Cloning.PhysicalFlatConverse.minimaxValue_tendsto
#check Cloning.PhysicalFlatGrassmann.minimaxValue_tendsto
#check Cloning.TensorCloning.eventually_rankFlat_minimaxValue_lower

#check Cloning.PhysicalFlatGrassmann.rankFlatChannel_uniform

#check Cloning.TensorLie.tensorFlatYoungPMF_dimension_moments_isBigO
#check Cloning.PhysicalFlatConverse.eventually_minimaxValue_rate
#check Cloning.PhysicalFlatConverse.eventually_minimaxValue_bounded_rounding_rate
#check Cloning.PhysicalFlatConverse.minimaxValue_upper_excess_isBigO

#check Cloning.TensorCloning.rankFlatChannel_tensorProjector
#check Cloning.TensorCloning.rankFlatChannel_eq_rankOnePCT_tensorProjector

#check Cloning.TensorLie.sectorGibbsDensity_padSpectrum
#check Cloning.TensorLie.physicalCartanMatrixChannel_rank_supported_compression
#check Cloning.TensorLie.nonnegativeCartanGibbsFidelity_padSpectrum
