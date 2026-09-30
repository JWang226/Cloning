import Cloning.InfiniteLANTransfer

/-!
# Quantum-channel LAN and minimax transfer

The Hilbert-space channel-composition fidelity estimate and minimax-to-Bayes bound are
proved using actual quantum channel laws. Physical forward/reverse LAN channels, their
uniform approximation errors, payoff integrability, the continuous classical-quantum
register model, and the Gaussian optimization input are not established by this transfer
theorem.

This public entry point adds no definitions or proofs. The declarations below locate the
principal result and its supporting statements in the checked library.
-/

#check Cloning.InfiniteLANTransfer.fidelity_transfer
#check Cloning.InfiniteLANTransfer.minimax_le_bayesValue
