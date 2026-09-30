import Cloning.MatrixFidelityProjector
import Cloning.YoungDimensionRatio
import Cloning.YoungDimensionSecondOrder

/-!
# Projector converse and dimension factors

The actual finite Kraus-channel projector converse and explicit crossing-root dimension-
product asymptotics are proved. The invariant physical block decomposition,
representation-dimension identification, and arbitrary-rank Young-law input remain
separate.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.MatrixFidelity.finite_kraus_projector_converse
#check Cloning.YoungDimensionRatio.projector_sector_factor_tendsto
