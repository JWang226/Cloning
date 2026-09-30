import Cloning.MatrixCovariantBalance
import Cloning.MatrixFidelityAsymptotics
import Cloning.MatrixTransitionAchievability

/-!
# Lifted-sector fidelity and achievability

Concrete matrix channel construction, lifted fidelity factorization, deletion control,
and achievability propagation are proved. Physical Schur/Cartan identification,
retained-sector approximation, discarded-mass estimates, and label limits remain inputs.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.MatrixFidelity.lifted_matrix_factorization_bound
#check Cloning.MatrixCovariantBalance.cartanChannel_of_irreducible_intertwiner
#check Cloning.MatrixFidelity.lifted_matrix_fidelity_converges
#check Cloning.MatrixTransitionAchievability.transition_achievability_bound
