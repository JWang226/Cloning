import Cloning.TensorCloningLiftedFactorization
import Cloning.PBWSymmetricFrameRateGram
import Cloning.PBWSymmetricFrameRateCartan
import Cloning.TensorCloningShrinkingWindows
import Cloning.YoungUniformCharacterWindows
import Cloning.TensorCartanChannel
import Cloning.MatrixLiftedCPTPPhysical
import Cloning.TensorCyclicSectorIrreducible
import Cloning.TensorHighestGramCovariance
import Cloning.TensorCartanIntertwiner
import Cloning.MatrixCovariantBalance
import Cloning.MatrixFidelityAsymptotics
import Cloning.MatrixTransitionAchievability
import Cloning.PBWRootGram
import Cloning.PBWGramLimit
import Cloning.TensorLieFiltration
import Cloning.TensorCyclicIndependence
import Cloning.TensorSchurDecompositionIsometry
import Cloning.TensorFundamentalBranchingExistence
import Cloning.TensorPBWCutoffBasis
import Cloning.TensorCartanMatrixLimit
import Cloning.TensorWeightFrameLimit
import Cloning.TensorSchurDecompositionMultiplicity
import Cloning.TensorCartanStateFidelity
import Cloning.TensorCloningGlobalCovariance
import Cloning.InfiniteFidelityHilbertSum

/-!
# Lifted-sector fidelity, PBW bounds, and achievability

Concrete matrix channel construction, fidelity factorization, deletion control, and
achievability propagation are proved. Exact normal ordering gives the Wick Gram
limit from local root/CCR defects and vacuum data, with the fine-to-grouped cutoff
transfer proved. Literal finite tensor-slot generators satisfy the exact collective
gl commutators, adjoint relations, norm bounds, and Cartan occupancy action. The
normalized highest tensor is constructed for every finite partition. Its actual
cyclic lowering-word filtration gives occupancy and raw-root estimates, quantitative
normalized CCR defects, and the physical finite-word PBW Gram bound. Retained roots
must have positive gaps; the cutoff is total positive-root height. The actual cyclic sector is irreducible under the literal generators. Exact
highest-weight Gram identities give full cyclic isometries and literal tensor-power
covariance; the constructed Cartan inclusion intertwines every generator. Actual partial-trace balance constructs a CPTP Cartan channel on these physical
cyclic sectors, using their actual finite dimensions. The
lifted protocol is an all-input CPTP channel with the exact earlier state formula.
The actual full tensor register has an exhaustive orthogonal Schur transform,
and physical one-box branching is constructed. Ordered PBW straightening proves
cutoff completeness and eventual bases; literal weight-preserving orthogonalization
converges to the normalized words. Exact Cartan splitting gives the fixed-word
matrix limits. Actual multiplicities, Weyl characters and dimensions, Gibbs
states, and Cartan output fidelity limits are proved. The known and universal
global channels are exactly unitary-covariant on all complex inputs. Actual
orthogonal Schur-copy fidelity is additive, including unnormalized blocks.

This entry point adds no definitions or proofs.
-/

#check Cloning.MatrixFidelity.lifted_matrix_factorization_bound
#check Cloning.MatrixCovariantBalance.cartanChannel_of_irreducible_intertwiner
#check Cloning.MatrixFidelity.lifted_matrix_fidelity_converges
#check Cloning.MatrixTransitionAchievability.transition_achievability_bound
#check Cloning.PBW.normalized_gram_error_le_of_root_filtration
#check Cloning.PBW.normalized_gram_tendsto_of_cutoff
#check Cloning.TensorLie.slotGenerator_apply
#check Cloning.TensorLie.collectiveGenerator_adjoint
#check Cloning.TensorLie.collectiveGenerator_commutator
#check Cloning.TensorLie.collectiveGenerator_diagonal
#check Cloning.TensorLie.highestTensor_norm
#check Cloning.TensorLie.highestTensor_raising_zero
#check Cloning.TensorLie.highestTensor_cartan
#check Cloning.TensorLie.collectiveGenerator_lowers_cutoff
#check Cloning.TensorLie.collectiveGenerator_raises_cutoff
#check Cloning.TensorLie.exists_partitionHighestTensor
#check Cloning.TensorLie.normalized_CCR_norm_le
#check Cloning.TensorLie.partition_normalized_gram_error_le
#check Cloning.TensorLie.partition_normalized_gram_tendsto
#check Cloning.TensorLie.partition_normalized_gramMatrix_tendsto
#check Cloning.TensorLie.partition_normalizedWord_eventually_linearIndependent
#check Cloning.TensorLie.tensorSchurTransform
#check Cloning.TensorLie.tensorSchurTransform_intertwines
#check Cloning.TensorLie.partition_eventually_canonicalCutoffBasis
#check Cloning.TensorLie.gramSchmidtNormed_sub_tendsto_zero
#check Cloning.TensorLie.cartanWordMatrixElement_tendsto

#check Cloning.TensorLie.partition_cyclicSector_irreducible
#check Cloning.TensorLie.highest_loweringWord_gram_eq
#check Cloning.TensorLie.highestCyclicIsometry
#check Cloning.TensorLie.highestCyclicIsometry_tensorOperator
#check Cloning.TensorLie.cyclicUnitary
#check Cloning.TensorLie.cartanInclusion
#check Cloning.TensorLie.cartanInclusion_intertwines
#check Cloning.TensorLie.cartanAmbientInclusion_range
#check Cloning.MatrixLiftedCPTP.channel
#check Cloning.MatrixLiftedCPTP.registerChannel
#check Cloning.MatrixLiftedCPTP.physicalChannel
#check Cloning.MatrixLiftedCPTP.physicalChannel_weightedInput

#check Cloning.TensorLie.physicalCartanBalance
#check Cloning.TensorLie.physicalCartanMatrixChannel
#check Cloning.TensorLie.physicalCartanChannel
#check Cloning.TensorLie.physicalCartanChannel_partitionMatrixOperator
#check Cloning.TensorLie.recursivePhysicalDecomposition_copyCount
#check Cloning.TensorLie.cartanGibbsPositive_rootFidelity_tendsto
#check Cloning.TensorCloning.universalChannel_covariant
#check Cloning.InfiniteFidelityHilbertSum.rootFidelity_orthogonalSum

#check Cloning.TensorLie.eventually_weightGram_rate
#check Cloning.TensorLie.eventually_weightSymmetricBasis_rate
#check Cloning.TensorLie.eventually_cartan_symmetricFrame_product_rate
#check Cloning.TensorCloning.eventually_uniform_shrinkingWindow_mixture_fidelity
#check Cloning.TensorCloning.eventually_uniform_shrinkingWindow_sector_fidelity
#check Cloning.TensorCloning.eventually_uniform_shrinkingWindow_compatible
#check Cloning.YoungMultinomial.eventually_uniform_character_normalization

#check Cloning.TensorCloning.eventually_uniform_lifted_fidelity_factorization
