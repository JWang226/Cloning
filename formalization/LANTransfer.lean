import Cloning.InfiniteLANTransfer
import Cloning.GeneralCoherentChannels
import Cloning.HybridJensenSigmaFinite

/-!
# Quantum-channel LAN and statistical transfer

The channel-composition fidelity estimate and minimax-to-Bayes bound use actual
quantum channel laws. Pure product states now have constructed two-way coherent
comparison channels in arbitrary finite dimension, uniformly on compact windows.
The continuous classical-quantum register model is constructed. Mixed-state forward
and reverse LAN channels, uniform Schur-sector approximation, and the universal
Gaussian optimization theorem remain necessary for the physical cloning application.

This entry point adds no definitions or proofs.
-/

#check Cloning.InfiniteLANTransfer.fidelity_transfer
#check Cloning.InfiniteLANTransfer.minimax_le_bayesValue
#check Cloning.GeneralCoherent.exists_twoWay_coherent_product_channels
#check Cloning.Hybrid.PositiveField.integral_fidelity_le_fidelity_integral
