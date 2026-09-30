import Cloning.InfiniteOccupationStates
import Cloning.ComplexCoherent

/-!
# Werner occupation and coherent-product limits

The actual normalized Werner binomial-ratio laws converge in trace norm to thermal
occupation operators. The constructed CPTP occupation channel also approximates the
normalized complex coherent product for every fixed amplitude in the explicit two-level
tensor realization. Physical Werner-output identification, general physical symmetric-
tensor embeddings, and uniform LAN estimates remain separate.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.InfiniteOccupationStates.occupation_traceNorm_tendsto
#check Cloning.ComplexCoherent.occupationChannel_coherent_product_tendsto
