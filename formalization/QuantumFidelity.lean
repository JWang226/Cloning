import Cloning.InfiniteChannelFidelity
import Cloning.InfiniteFidelityContinuity
import Cloning.InfiniteFidelityRegularized
import Cloning.InfiniteFidelityConcavity
import Cloning.HybridWeightedFidelity
import Cloning.HybridJensenSigmaFinite

/-!
# Quantum and continuous classical-quantum fidelity

Actual positive trace-class operators satisfy data processing, continuity, deletion,
weighted bounds, and joint concavity. Integrable positive operator fields provide a
continuous classical-quantum model with L1 norm, fidelity continuity, fibrewise CPTP
data processing, and sigma-finite Bochner Jensen. The weighted product-target bound
uses explicit finite RHS integrals and a uniform regularized inverse-moment bound;
application-specific witness moments still need to be established.

This entry point adds no definitions or proofs.
-/

#check Cloning.InfiniteFidelity.fidelity_data_processing
#check Cloning.InfiniteFidelity.stateFidelity_continuity
#check Cloning.InfiniteFidelity.fidelity_weighted_joint_concavity
#check Cloning.Hybrid.PositiveField.rootFidelity_continuity
#check Cloning.Hybrid.PositiveField.integral_fidelity_le_fidelity_integral
#check Cloning.Hybrid.PositiveField.rootFidelity_sq_le_weighted_product
