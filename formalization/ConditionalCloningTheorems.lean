import Cloning.Main

/-!
# Conditional main cloning assembly and scalar PCT comparison

Known- and unknown-spectrum minimax convergence follows from explicit supplied
achievability and converse bounds. These are not end-to-end proofs of the physical
cloning theorems. The strict PCT-versus-universal comparison of the explicit scalar
limiting formulas is proved; convergence of the actual finite-sample PCT output to that
formula remains separate.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.known_spectrum_optimum_of_bounds
#check Cloning.unknown_spectrum_optimum_of_bounds
#check Cloning.pctValue_lt_universalValue
