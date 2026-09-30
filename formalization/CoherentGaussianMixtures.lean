import Cloning.MultimodeCoherentGaussianMixture
import Cloning.InfiniteDiagonalFidelity

/-!
# Coherent Gaussian mixtures are thermal operators

The literal finite product circular Gaussian mixture of normalized coherent projectors
equals the product geometric operator as a trace-class Bochner integral. Every
coordinate variance is positive; the empty product with zero modes is also covered.
Actual thermal state fidelity is computed. This does not identify the physical PCT output or construct a general physical
occupation embedding.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.MultimodeCoherentGaussianMixture.integral_coherentProjector_gaussian_eq_productThermal
#check Cloning.InfiniteDiagonalFidelity.stateFidelity_productGeometric
